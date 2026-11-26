-- Prove2me | Theorems.Thm_Malliavin_norm_multipleIntegralCLM
-- name    : Malliavin.norm_multipleIntegralCLM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:29.67497+00:00
-- url     : https://prove2.me/theorems/a628eb23-e845-4ce7-9329-f149f99aa155
-- title:
--   Malliavin: norm multiple Integral CLM
-- statement:
--   Exact norm of the selected multiple operator.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L156-L162
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L156-L162

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.norm_multipleIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    ‖multipleIntegralCLM hB n f‖ = Real.sqrt (n.factorial : ℝ) *
      ‖symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f‖ := by sorry
