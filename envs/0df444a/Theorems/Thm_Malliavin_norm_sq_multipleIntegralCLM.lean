-- Prove2me | Theorems.Thm_Malliavin_norm_sq_multipleIntegralCLM
-- name    : Malliavin.norm_sq_multipleIntegralCLM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:49:32.406872+00:00
-- url     : https://prove2.me/theorems/859dac3e-935f-5884-b60d-dd0e75b4362e
-- title:
--   Malliavin: norm sq multiple Integral CLM
-- statement:
--   Squared-norm form of the selected-operator isometry.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L149-L153
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L149-L153

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.norm_sq_multipleIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    ‖multipleIntegralCLM hB n f‖ ^ 2 = (n.factorial : ℝ) *
      ‖symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f‖ ^ 2 := by sorry
