-- Prove2me | Theorems.Thm_Malliavin_multipleIntegralCLM_eq_zero_iff
-- name    : Malliavin.multipleIntegralCLM_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:08:02.643233+00:00
-- url     : https://prove2.me/theorems/7b91bdd9-d9a2-5c5d-a1eb-51012153f9b1
-- title:
--   Malliavin: multiple Integral CLM eq zero iff
-- statement:
--   The kernel of `Iₙ` is exactly the kernel of symmetrization.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L200-L214
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L200-L214

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.multipleIntegralCLM_eq_zero_iff (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    multipleIntegralCLM hB n f = 0 ↔
      symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f = 0 := by sorry
