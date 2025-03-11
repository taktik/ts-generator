/*
 * Copyright 2017 Alicia Boya García
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package me.ntrrgc.tsGenerator

import java.beans.Introspector
import java.lang.reflect.ParameterizedType
import java.lang.reflect.Type
import kotlin.reflect.KCallable
import kotlin.reflect.KClass
import kotlin.reflect.KProperty
import kotlin.reflect.KType
import kotlin.reflect.KTypeParameter
import kotlin.reflect.KVisibility
import kotlin.reflect.full.allSuperclasses
import kotlin.reflect.full.createType
import kotlin.reflect.full.declaredMemberProperties
import kotlin.reflect.full.isSubclassOf
import kotlin.reflect.full.memberProperties
import kotlin.reflect.jvm.javaType

/**
 * TypeScript definition generator.
 *
 * Generates the content of a TypeScript definition file (.d.ts) that
 * covers a set of Kotlin and Java classes.
 *
 * This is useful when data classes are serialized to JSON and
 * handled in a JS or TypeScript web frontend.
 *
 * Supports:
 *  * Primitive types, with explicit int
 *  * Kotlin and Java classes
 *  * Data classes
 *  * Enums
 *  * Any type
 *  * Generic classes, without type erasure
 *  * Generic constraints
 *  * Class inheritance
 *  * Abstract classes
 *  * Lists as JS arrays
 *  * Maps as JS objects
 *  * Null safety, even inside composite types
 *  * Java beans
 *  * Mapping types
 *  * Customizing class definitions via transformers
 *  * Parenthesis are placed only when they are needed to disambiguate
 *
 * @constructor
 *
 * @param rootClasses Initial classes to traverse. Enough definitions
 * will be created to cover them and the types of their properties
 * (and so on recursively).
 *
 * @param mappings Allows to map some JVM types with JS/TS types. This
 * can be used e.g. to map LocalDateTime to JS Date.
 *
 * @param mappingsKtToTs Allows to map some KT name class into TS name Class.
 *
 * @param classTransformers Special transformers for certain subclasses.
 * They allow to filter out some classes, customize what methods are
 * exported, how they names are generated and what types are generated.
 *
 * @param ignoreSuperclasses Classes and interfaces specified here will
 * not be emitted when they are used as superclasses or implemented
 * interfaces of a class.
 *
 * @param intTypeName Defines the name integer numbers will be emitted as.
 * By default it's number, but can be changed to int if the TypeScript
 * version used supports it or the user wants to be extra explicit.
 *
 * @param flags The first value in the list represents the
 * possibility to use set<T> in typeScript and not arrays.
 * The second value represents the possibility to use enum as classes
 */
class TypeScriptGenerator(
    rootClasses: Iterable<KClass<*>>,
    private val mappings: Map<KClass<*>, String> = mapOf(),
    private val mappingsKtToTs: Map<KClass<*>, String> = mapOf(),
    classTransformers: List<ClassTransformer> = listOf(),
    ignoreSuperclasses: Set<KClass<*>> = setOf(),
    private val intTypeName: String = "number",
    private val voidType: VoidType = VoidType.NULL,
    private val flags: List<Boolean> = listOf(false,false),
    private val interfacesPrefixes: String? = "",
    private val extraSuperTypes: ((KClass<*>) -> Set<KType>) = { _ -> emptySet() },
    private val includeOverriddenProperties: Boolean = false,
) {
    private val visitedClasses: MutableSet<KClass<*>> = java.util.HashSet()
    private val generatedDefinitions = mutableMapOf<KClass<*>, String>()
    private val pipeline = ClassTransformerPipeline(classTransformers)
    private val ignoredSuperclasses = setOf(
        Any::class,
        java.io.Serializable::class,
        Comparable::class
    ).plus(ignoreSuperclasses)

    init {
        rootClasses.forEach { visitClass(it) }
    }

    companion object {
        private val KotlinAnyOrNull = Any::class.createType(nullable = true)

        fun isJavaBeanProperty(kProperty: KProperty<*>, klass: KClass<*>): Boolean {
            val beanInfo = Introspector.getBeanInfo(klass.java)
            return beanInfo.propertyDescriptors
                .any { bean -> bean.name == kProperty.name }
        }
    }

    private fun visitClass(klass: KClass<*>) {
        if (klass !in visitedClasses) {
            visitedClasses.add(klass)
            generatedDefinitions[klass] = generateDefinition(klass)
        }
    }

    private fun formatClassType(type: KClass<*>): String {
        visitClass(type)
        return if (type.java.isEnum || type in ignoredSuperclasses) type.simpleName!! else interfacesPrefixes + type.simpleName!!
    }

    private fun formatKType(kType: KType): TypeScriptType {
        val classifier = kType.classifier
        if (classifier is KClass<*>) {
            val existingMapping = mappings[classifier]
            if (existingMapping != null) {
                return TypeScriptType.single(existingMapping, kType.isMarkedNullable, voidType)
            } else {// generate the based kotlin name class into the custom name in ts
                var existingNameInTypescript = mappingsKtToTs[classifier]
                if (existingNameInTypescript != null) {
                    visitClass(classifier)
                    existingNameInTypescript = if (classifier.java.isEnum || classifier in ignoredSuperclasses) existingNameInTypescript else interfacesPrefixes + existingNameInTypescript
                    return TypeScriptType.single( existingNameInTypescript + if (kType.arguments.isNotEmpty()) {
                        "<" + kType.arguments.joinToString(", ") { arg ->
                            formatKType(
                                arg.type ?: KotlinAnyOrNull
                            ).formatWithoutParenthesis()
                        } + ">"
                    } else "", kType.isMarkedNullable, voidType)
                }
            }
        }
        val classifierTsType = when (classifier) {
            Boolean::class -> "boolean"
            String::class, Char::class -> "string"
            Int::class,
            Long::class,
            Short::class,
            Byte::class -> intTypeName
            Float::class, Double::class -> "number"
            Any::class -> "any"
            else -> {
                @Suppress("IfThenToElvis")
                if (classifier is KClass<*>) {
                    if (flags[0] && classifier.isSubclassOf(Set::class)) {
                        // Use native JS associative object
                        val rawKeyType = kType.arguments[0].type ?: KotlinAnyOrNull
                        val keyType = formatKType(rawKeyType)
                        "Set<${keyType.formatWithoutParenthesis()}>"
                    }
                    else if (classifier.isSubclassOf(Iterable::class)
                        || classifier.javaObjectType.isArray)
                    {
                        // Use native JS array
                        // Parenthesis are needed to disambiguate complex cases,
                        // e.g. (Pair<string|null, int>|null)[]|null
                        val itemType = when (kType.classifier) {
                            // Native Java arrays... unfortunately simple array types like these
                            // are not mapped automatically into kotlin.Array<T> by kotlin-reflect :(
                            IntArray::class -> Int::class.createType(nullable = false)
                            ShortArray::class -> Short::class.createType(nullable = false)
                            ByteArray::class -> Byte::class.createType(nullable = false)
                            CharArray::class -> Char::class.createType(nullable = false)
                            LongArray::class -> Long::class.createType(nullable = false)
                            FloatArray::class -> Float::class.createType(nullable = false)
                            DoubleArray::class -> Double::class.createType(nullable = false)

                            // Class container types (they use generics)
                            else -> {
                                try {
                                    kType.arguments.single().type
                                } catch (e: Exception) {
                                    println("error in itemType $e")
                                    KotlinAnyOrNull
                                }

                            }
                        }
                        "${itemType?.let { formatKType(it).formatWithParenthesis() }}[]"
                    } else if (classifier.isSubclassOf(Map::class)) {
                        // Use native JS associative object
                        val rawKeyType = kType.arguments[0].type ?: KotlinAnyOrNull
                        val keyType = formatKType(rawKeyType)
                        val valueType = formatKType(kType.arguments[1].type ?: KotlinAnyOrNull)
                        if ((rawKeyType.classifier as? KClass<*>)?.java?.isEnum == true)
                            "{ [key in ${keyType.formatWithoutParenthesis().replace(" | ${VoidType.NULL.jsTypeName}", "")}]?: ${valueType.formatWithoutParenthesis()} }".replace("| ${VoidType.NULL.jsTypeName}", "| ${VoidType.UNDEFINED.jsTypeName}")
                        else
                            "{ [key: ${keyType.formatWithoutParenthesis()}]: ${valueType.formatWithoutParenthesis()} }".replace("| ${VoidType.NULL.jsTypeName}", "| ${VoidType.UNDEFINED.jsTypeName}")
                    } else {
                        // Use class name, with or without template parameters
                        formatClassType(classifier) + if (kType.arguments.isNotEmpty()) {
                            "<" + kType.arguments.joinToString(", ") { arg ->
                                formatKType(
                                    arg.type ?: KotlinAnyOrNull
                                ).formatWithoutParenthesis()
                            } + ">"
                        } else ""
                    }
                } else if (classifier is KTypeParameter) {
                    classifier.name
                } else {
                    "UNKNOWN" // giving up
                }
            }
        }
        return TypeScriptType.single(classifierTsType, kType.isMarkedNullable, voidType)
    }

    private fun generateEnum(klass: KClass<*>): String {
        return if (flags[1]) {
            "enum ${getKotlinNameToTypeScript(klass)} {\n" +
                    klass.java.enumConstants.joinToString("") { constant: Any ->
                        "    ${transformPropertyEnum(constant.toString())} = '${constant}',\n"
                    } +
            "}".replace("\t","    ")
        } else {
            "type ${getKotlinNameToTypeScript(klass)} = ${
                klass.java.enumConstants.joinToString(" | ") { constant: Any ->
                    constant.toString().toJSString()
                }
            };".replace("\t","    ")
        }


    }
    //add '' to an enum with a -
    private fun transformPropertyEnum(toString: String): String {
        if (toString.contains('-') || toString.matches(Regex("^[0-9].*"))) {
            return "'${toString.toUpperCase()}'"
        }
        return toString.toUpperCase()
    }

    private fun generateInterface(klass: KClass<*>): String {
        val supertypes = (klass.supertypes.filterNot { it.classifier in ignoredSuperclasses } + extraSuperTypes.invoke(klass)).toSet()
        val extendsString = if (supertypes.isNotEmpty()) {
            " extends " + supertypes.joinToString(", ") { formatKType(it).formatWithoutParenthesis() }
        } else ""

        val templateParameters = if (klass.typeParameters.isNotEmpty()) {
            "<" + klass.typeParameters.joinToString(", ") { typeParameter ->
                val bounds = typeParameter.upperBounds
                    .filter { it.classifier != Any::class }
                typeParameter.name + if (bounds.isNotEmpty()) {
                    " extends " + bounds.joinToString(" & ") { bound ->
                        formatKType(bound).formatWithoutParenthesis()
                    }
                } else {
                    ""
                }
            } + ">"
        } else {
            ""
        }
        val interfaceName = if ( klass in ignoredSuperclasses ) getKotlinNameToTypeScript(klass) else interfacesPrefixes + getKotlinNameToTypeScript(klass)
        return "interface $interfaceName$templateParameters$extendsString {\n" +
                klass.declaredMemberProperties
                    .filter { p -> includeOverriddenProperties || !klass.allSuperclasses.flatMap { it.declaredMemberProperties }.any { it.name == p.name && it.returnType == p.returnType }}
                    .filter { !isFunctionType(it.returnType.javaType) }
                    .filter {
                        it.visibility == KVisibility.PUBLIC || isJavaBeanProperty(it, klass)
                    }
                    .let { propertyList ->
                        pipeline.transformPropertyList(propertyList, klass)
                    }.joinToString("") { property ->
                        val propertyName = pipeline.transformPropertyName(property.name, property, klass)
                        val propertyType = pipeline.transformPropertyType(property.returnType, property, klass)
                        val formattedPropertyType = formatKType(propertyType).formatWithoutParenthesis()
                        val deprecated = property.annotations.find { it.annotationClass.simpleName == "Deprecated" }?.let { annotation ->
                            val msg = (annotation::class.memberProperties.find { it.name == "message" }?.getter?.call(annotation) as? String)?.takeIf { it.isNotBlank() }?.let { " $it" } ?: ""
                            "/** @deprecated$msg */\n"
                        } ?: ""
                        "$deprecated    $propertyName: $formattedPropertyType\n"
                    } +
            "}".replace("\t","    ")
    }

    private fun isFunctionType(javaType: Type): Boolean {
        return javaType is KCallable<*>
            || javaType.typeName.startsWith("kotlin.jvm.functions.")
            || (javaType is ParameterizedType && isFunctionType(javaType.rawType))
    }

    private fun generateDefinition(klass: KClass<*>): String {
        return if (klass.java.isEnum) {
            generateEnum(klass)
        } else {
            generateInterface(klass)
        }
    }

    private fun getKotlinNameToTypeScript(klass: KClass<*>): String?{
        val overriddenName = klass.annotations.find { it.annotationClass.simpleName == "TypeScriptClassName" }?.let { annotation -> annotation.annotationClass.memberProperties.firstOrNull { it.name == "name" } ?.call(annotation) } as? String
        return overriddenName ?: mappingsKtToTs[klass] ?: klass.simpleName
    }

    // Public API:
    val definitionsText: String
        get() = generatedDefinitions.values.joinToString("\n\n")

    val individualDefinitions: Set<String>
        get() = generatedDefinitions.values.toSet()

    fun generatedDefinitions() = generatedDefinitions
}
