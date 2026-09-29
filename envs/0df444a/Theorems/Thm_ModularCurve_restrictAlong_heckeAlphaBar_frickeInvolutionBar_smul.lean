-- Prove2me | Theorems.Thm_ModularCurve_restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul
-- name    : ModularCurve.restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/86df8bd1-fbdb-5490-8358-0791082fa4ca
-- title:
--   Fricke translation exchanges the two degeneracy restrictions
-- statement:
--   Let $q$ be a non-zero natural number. Work with the field $\overline{\mathbb{Q}}$-algebras obtained from the modular function fields: `modularFunctionFieldBar N` is the intermediate field `laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)` of $\overline{\mathbb{Q}}\,((q))$-type Laurent series, namely the subfield generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `modularFunctionFieldFull N`, the subfield of `LaurentSeries ℚ` generated over $\mathbb{Q}$ by the set `divisorExpansions N`. Two $\overline{\mathbb{Q}}$-algebra maps from level $1$ to level $1 \cdot q$ are involved: `heckeAlphaBar`, the inclusion coming from the containment of the level-$1$ field in the level-$(1\cdot q)$ field, and `heckeBetaBar`, induced by the substitution `qExpand` which multiplies all Laurent exponents by $q$. Assume `HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q` and `HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q`, i.e. that each of these two ring maps is integral. Let $W$ be a place of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb{Q}}$, that is, a valuation subring containing the image of $\overline{\mathbb{Q}}$, different from the whole field, and a principal ideal ring. Then the restriction of $\,$`frickeInvolutionBar (1 * q)` $\cdot\, W$ along `heckeAlphaBar` equals the restriction of $W$ along `heckeBetaBar`, where restriction along an integral algebra map is the contraction (comap) of the valuation subring, and `frickeInvolutionBar N` is the base change to $\overline{\mathbb{Q}}$, via `geomAut`, of the $\mathbb{Q}$-automorphism `frickeInvolutionFull N` of `modularFunctionFieldFull N`.
--
--   On points this is the classical relation $\pi_1 \circ w_q = \pi_2$ between the Fricke involution of $X_0(q)$ and the two degeneracy maps down to $X_0(1)$, here expressed for places of the corresponding function fields. It is used in the analysis of prolongations of level-one places to level $q$, in particular in the cusp and divisor laws for prolongation pairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul (q : ℕ) [NeZero q]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    (frickeInvolutionBar (1 * q) • W).restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα
      = W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ := by sorry
