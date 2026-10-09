-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_finite_map_data_arbitrarily_large_charZero
-- name    : MazurTransfer.order13_actual_finite_map_data_arbitrarily_large_charZero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T09:37:09.795836+00:00
-- url     : https://prove2.me/theorems/dcdaeffa-00c4-47b3-9c72-cffb4a0813ab
-- title:
--   Finite-map data of arbitrarily large degree on the actual order-13 curve
-- statement:
--   Let $K$ be any characteristic-zero field, and let $C/K$ be the unchanged two-chart curve
--   $$y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1,$$
--   with reciprocal coordinates $z=x^{-1}$ and $w=yx^{-3}$. For any $K$-rational section $\varepsilon$ and any nonnegative integer $m_0$, there is genuine finite-map data on $(C,\varepsilon)$ with degree $m$ satisfying
--   $$m_0\le m,\qquad m\in K^\times.$$
--   This includes two affine opens covering $C$, reciprocal regular functions on their overlap, the complement of $\varepsilon$ as one chart, finite polynomial-algebra maps, and the required free rank-$m$ level sets after local algebra base change.
--
--   In particular the result holds over $\mathbb Q$. These data supply the actual-curve input for finite etale Picard charts and descent to a rational Picard representation.
-- source:
--   Actual curve and gluing: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry . Exact finite-map criterion: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_finiteMapData_le_isUnit_of_twoAffineOpenCover.lean . Actual model, geometric integrality and cover assembly by Vas and contributors. Apache-2.0 attribution retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra

theorem MazurTransfer.order13_actual_finite_map_data_arbitrarily_large_charZero.{u} (K : Type u) [Field K] [CharZero K]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)) (m₀ : ℕ) :
    ∃ 𝔉 : SmoothProperCurve.FiniteMapData
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε,
      m₀ ≤ 𝔉.m ∧ IsUnit (𝔉.m : K) := by sorry
