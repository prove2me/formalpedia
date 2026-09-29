-- Prove2me | Theorems.Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg
-- name    : ModularCurve.eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/67759593-69b4-5c4a-8db6-973f07b7f520
-- title:
--   Poles of j on X₀(q)_ℚ̄ lie at the two cusps
-- statement:
--   Let $q$ be a prime and let $F =$ `modularFunctionFieldBar (1 * q)` be the base change to $\overline{\mathbb Q}$ of the full modular function field of level $1 \cdot q$, realised as an intermediate field of the Laurent series field $\overline{\mathbb Q}((\mathfrak q))$ over $\overline{\mathbb Q}$. Let $W$ be a place of $F$ over $\overline{\mathbb Q}$ in the sense of the project's `Place` structure, that is, a valuation subring of $F$ that contains the image of $\overline{\mathbb Q}$, is not all of $F$, and is a principal ideal ring. Assume that $W.\mathrm{ord}$ of the element `PlaceSpecialization.jFun` is strictly negative, where `jFun` is the element of $F$ obtained from the $\mathfrak q$-expansion `jq` of the modular invariant $j$ by coefficient extension to $\overline{\mathbb Q}$, and $W.\mathrm{ord}$ denotes minus the logarithm of the associated adic valuation. Then $W$ is one of two distinguished places: either $W =$ `cuspInftyBar (1 * q)`, the place at $\mathfrak q = \infty$ cut out by the $\mathfrak q$-expansion of $j$, or $W =$ `cuspZeroBar (1 * q)`, the translate of that place under the action of the Fricke involution `frickeInvolutionBar (1 * q)`.
--
--   This is the statement that $j$ has poles only at the two cusps $\bar\infty$ and $\bar 0$ of $X_0(q)$ over $\overline{\mathbb Q}$, in the form needed for the level-$1\cdot q$ spelling of the modular function field used in the construction of place specialisations. It is used in the analysis of prolongation pairs at level one, in particular in the lemmas producing admissible representatives of cuspidal classes and elements of Riemann–Roch spaces with prescribed pole order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg {q : ℕ} [Fact q.Prime] (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : W.ord (PlaceSpecialization.jFun (q := q)) < 0) : W = cuspInftyBar (1 * q) ∨ W = cuspZeroBar (1 * q) := by sorry
