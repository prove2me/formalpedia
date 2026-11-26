-- Prove2me | Theorems.Thm_Malliavin_inner_multipleIntegralCLM
-- name    : Malliavin.inner_multipleIntegralCLM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:49:55.193736+00:00
-- url     : https://prove2.me/theorems/97669caf-e3cb-491b-b741-6eac4a8a2662
-- title:
--   Malliavin: inner multiple Integral CLM
-- statement:
--   Same-order isometry for the selected multiple operators, in polarized form.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L124-L137
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L124-L137

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.inner_multipleIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ)
    (f g : IteratedKernel n) :
    inner ℝ (multipleIntegralCLM hB n f) (multipleIntegralCLM hB n g) =
      (n.factorial : ℝ) * inner ℝ
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f)
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g) := by sorry
