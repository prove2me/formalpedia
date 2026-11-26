-- Prove2me | Theorems.Thm_Malliavin_integral_cov_sub
-- name    : Malliavin.integral_cov_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:47:11.216714+00:00
-- url     : https://prove2.me/theorems/f1d95658-df2b-58dd-bdec-02e89c653c0d
-- title:
--   Malliavin: integral cov sub
-- statement:
--   Expansion of the covariance of two increments via bilinearity.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L93-L115
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L93-L115

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

theorem Malliavin.integral_cov_sub (hW : IsWienerCov W) (u v x y : ℝ≥0) :
    ∫ z, (W v z - W u z) * (W y z - W x z)
        = min v y - min v x - min u y + min u x := by sorry
