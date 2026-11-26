-- Prove2me | Theorems.Thm_Malliavin_multipleIntegralCLM_symmetrize
-- name    : Malliavin.multipleIntegralCLM_symmetrize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:23.777823+00:00
-- url     : https://prove2.me/theorems/83bfee2a-bb4c-4121-98b7-4afe9ea68bfb
-- title:
--   Malliavin: multiple Integral CLM symmetrize
-- statement:
--   The selected multiple operator only depends on the symmetric part of its kernel.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L96-L102
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L96-L102

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.multipleIntegralCLM_symmetrize (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    multipleIntegralCLM hB n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f) =
      multipleIntegralCLM hB n f := by sorry
