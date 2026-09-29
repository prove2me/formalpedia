-- Prove2me | Theorems.Thm_ModularCurve_coeffMap_mem_laurentBaseChange_of_ringHom
-- name    : ModularCurve.coeffMap_mem_laurentBaseChange_of_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/9a8e6664-8972-5e9c-9a5c-efe65bb5e61c
-- title:
--   Coefficientwise maps preserve constant-field extensions of a Laurent subfield
-- statement:
--   Let $L_1$ and $L_2$ be fields equipped with $\mathbb{Q}$-algebra structures, let $\sigma : L_1 \to L_2$ be a ring homomorphism (automatically compatible with the structure maps from $\mathbb{Q}$, these being the unique ring homomorphisms out of $\mathbb{Q}$), and let $F_0$ be an intermediate field between $\mathbb{Q}$ and the field $\mathbb{Q}((q))$ of formal Laurent series over $\mathbb{Q}$. For a field $L$ over $\mathbb{Q}$, write `laurentBaseChange L F₀` for the intermediate field between $L$ and $L((q))$ obtained by adjoining to $L$ the image of the underlying set of $F_0$ under `coeffEmb L`, the ring homomorphism $\mathbb{Q}((q)) \to L((q))$ applying $\operatorname{algebraMap} \mathbb{Q} L$ to every coefficient; and write `coeffMap σ` for the ring homomorphism $L_1((q)) \to L_2((q))$ applying $\sigma$ to every coefficient. The assertion is that for every $x \in L_1((q))$ lying in `laurentBaseChange L₁ F₀`, the series `coeffMap σ x` lies in `laurentBaseChange L₂ F₀`. Thus the coefficientwise action of $\sigma$ carries the constant-field extension of $F_0$ by $L_1$ into that by $L_2$.
--
--   This is the functoriality of constant-field extension with respect to change of the field of constants, in the concrete setting of subfields of formal Laurent series over $\mathbb{Q}$. It is used when transporting $q$-expansions and places along a change of coefficient field, for instance in the construction of places of $L((q))$-base-changed modular function fields of residue degree one and in the estimates for hyperplane sections on the modular curves considered here.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeffMap_mem_laurentBaseChange_of_ringHom.lean

import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.coeffMap_mem_laurentBaseChange_of_ringHom {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra ℚ L₁] [Algebra ℚ L₂] (σ : L₁ →+* L₂) (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) {x : LaurentSeries L₁} (hx : x ∈ ModularCurve.laurentBaseChange L₁ F₀) : ModularCurve.coeffMap σ x ∈ ModularCurve.laurentBaseChange L₂ F₀ := by sorry
