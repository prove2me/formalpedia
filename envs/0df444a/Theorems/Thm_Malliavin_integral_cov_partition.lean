-- Prove2me | Theorems.Thm_Malliavin_integral_cov_partition
-- name    : Malliavin.integral_cov_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:48:45.597365+00:00
-- url     : https://prove2.me/theorems/24918fed-487b-53d7-936f-bcd2f1052014
-- title:
--   Malliavin: integral cov partition
-- statement:
--   Covariance of increments along a partition: the diagonal carries the
--   interval length, off-diagonal terms vanish.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L157-L171
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L157-L171

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral
set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
variable {W : ℝ≥0 → Ω → ℝ}

theorem Malliavin.integral_cov_partition (hW : IsWienerCov W) {n : ℕ} (P : Partition n) (i j : Fin n) :
    ∫ z, (W (P.t i.succ) z - W (P.t i.castSucc) z) *
          (W (P.t j.succ) z - W (P.t j.castSucc) z)
      = if i = j then (P.t i.succ : ℝ) - (P.t i.castSucc : ℝ) else 0 := by sorry
