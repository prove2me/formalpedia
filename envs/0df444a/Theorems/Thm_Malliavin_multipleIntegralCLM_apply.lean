-- Prove2me | Theorems.Thm_Malliavin_multipleIntegralCLM_apply
-- name    : Malliavin.multipleIntegralCLM_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:49:45.5478+00:00
-- url     : https://prove2.me/theorems/d39ad10c-5651-423f-9778-4c284f14a6c1
-- title:
--   Malliavin: multiple Integral CLM apply
-- statement:
--   Evaluation formula for `Iₙ`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L88-L93
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L88-L93

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.multipleIntegralCLM_apply (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    multipleIntegralCLM hB n f = (n.factorial : ℝ) •
      iteratedIntegralCLM hB n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f) := by sorry
