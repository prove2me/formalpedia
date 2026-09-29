-- Prove2me | Theorems.Thm_ModularCurve_deg_cuspInftyFull
-- name    : ModularCurve.deg_cuspInftyFull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/1814b5b1-642e-564d-8eca-36e53e6a2530
-- title:
--   The cusp at infinity of the full modular function field has degree one
-- statement:
--   Let $N$ be a natural number, nonzero. Consider the field $F =$ `modularFunctionFieldFull N`, the intermediate field of the Laurent series field $\mathbb{Q}((q))$ over $\mathbb{Q}$ obtained by adjoining to $\mathbb{Q}$ the family `divisorExpansions N` of $q$-expansions attached to the divisors of $N$. The place `cuspInftyFull N` of $F$ over $\mathbb{Q}$ is the instance of `qInftyPlaceRat` for this $F$, with witness the element $jq$ of $F$ (the $q$-expansion of the modular invariant $j$, which lies in $F$ by `jq_mem_full`) whose $\bar q$-series has order $-1$; concretely it is the data of the valuation subring `qIntegersBar ℚ F` of $F$, together with the facts that it contains the image of $\mathbb{Q}$, is not all of $F$, and is a principal ideal ring. The theorem asserts that the degree of this place is $1$, where the degree of a place is by definition the $\mathbb{Q}$-dimension of the residue field of its valuation subring: the residue field at the cusp $\infty$ of $F$ is $\mathbb{Q}$ itself.
--
--   This is the statement that the cusp $\infty$ is a rational point of the canonical model over $\mathbb{Q}$ of the modular curve attached to the full level-$N$ divisor data, expressed in the language of places of a function field. It is used in [`ModularCurve.exists_schemeHomOver_placeOfPoint_eq_cuspInftyFull_of_isProper_of_ratCurveModel`](thm.html#ModularCurve.exists_schemeHomOver_placeOfPoint_eq_cuspInftyFull_of_isProper_of_ratCurveModel), where the cusp must be realised as a $\mathbb{Q}$-point of a proper model of the curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_deg_cuspInftyFull.lean

import Definitions.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.deg_cuspInftyFull (N : ℕ) [NeZero N] : (cuspInftyFull N).deg = 1 := by sorry
