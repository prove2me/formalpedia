-- Prove2me | Theorems.Thm_Malliavin_inner_multipleIntegralCLM_of_fixed
-- name    : Malliavin.inner_multipleIntegralCLM_of_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:07:36.020483+00:00
-- url     : https://prove2.me/theorems/8ca944e1-b0b8-439b-98d0-09d171d4e465
-- title:
--   Malliavin: inner multiple Integral CLM of fixed
-- statement:
--   On symmetric kernels, the same-order isometry has its conventional `n!` normalization.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L140-L146
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L140-L146

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.inner_multipleIntegralCLM_of_fixed (hB : IsPreBrownianReal B P) (n : ℕ)
    (f g : IteratedKernel n)
    (hf : symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f = f)
    (hg : symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g = g) :
    inner ℝ (multipleIntegralCLM hB n f) (multipleIntegralCLM hB n g) =
      (n.factorial : ℝ) * inner ℝ f g := by sorry
