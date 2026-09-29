-- Prove2me | Theorems.Thm_ModularCurve_coeffMap_coeffEmb_of_ringHom
-- name    : ModularCurve.coeffMap_coeffEmb_of_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/3f193eb6-c450-541a-96be-e46b7459cada
-- title:
--   Ring homomorphisms intertwine the coefficient embeddings of ℚ((q))
-- statement:
--   Let $L_1$ and $L_2$ be fields, each carrying an algebra structure over $\mathbb{Q}$, and let $\sigma : L_1 \to L_2$ be a ring homomorphism (not assumed compatible with the $\mathbb{Q}$-structures). For a commutative ring homomorphism $f : R \to S$, [`ModularCurve.coeffMap f`](def/ModularCurve_LaurentCoeff.html#L16) denotes the ring homomorphism $\mathrm{LaurentSeries}\,R \to \mathrm{LaurentSeries}\,S$ obtained by applying $f$ to each coefficient, i.e. by `HahnSeries.map`; for a field $L$ over $\mathbb{Q}$, [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) is the ring homomorphism $\mathbb{Q}((q)) \to L((q))$ given by `coeffMap` applied to the structure map $\mathbb{Q} \to L$. The assertion is that for every formal Laurent series $x$ with rational coefficients, pushing $x$ into $L_1((q))$ by `coeffEmb L₁` and then applying $\sigma$ coefficientwise yields exactly the image of $x$ under `coeffEmb L₂`: $$\mathrm{coeffMap}\,\sigma\bigl(\mathrm{coeffEmb}\,L_1\,x\bigr) = \mathrm{coeffEmb}\,L_2\,x.$$ Equivalently, the triangle formed by the two coefficient embeddings of $\mathbb{Q}((q))$ and the coefficientwise map induced by $\sigma$ commutes pointwise, which reflects the fact that the two ring homomorphisms $\mathbb{Q} \to L_2$, namely $\sigma$ composed with the structure map of $L_1$ and the structure map of $L_2$, coincide.
--
--   This is the functoriality of the coefficientwise embedding of $\mathbb{Q}((q))$ into $L((q))$ in the coefficient field, resting on the uniqueness of a $\mathbb{Q}$-algebra structure on a field. It is used when $q$-expansions of modular functions are compared across varying coefficient fields, for instance in the analysis of places of the Laurent base change of modular function fields and in the constructions attached to full level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeffMap_coeffEmb_of_ringHom.lean

import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.coeffMap_coeffEmb_of_ringHom {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra ℚ L₁] [Algebra ℚ L₂] (σ : L₁ →+* L₂) (x : LaurentSeries ℚ) : ModularCurve.coeffMap σ (ModularCurve.coeffEmb L₁ x) = ModularCurve.coeffEmb L₂ x := by sorry
