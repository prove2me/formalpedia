-- Prove2me | Theorems.Thm_Malliavin_norm_multipleIntegralCLM_le
-- name    : Malliavin.norm_multipleIntegralCLM_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:07:47.361826+00:00
-- url     : https://prove2.me/theorems/dc72936c-6d0b-5658-a978-449bb93c9c78
-- title:
--   Malliavin: norm multiple Integral CLM le
-- statement:
--   Operator-level bound inherited from the symmetrization contraction.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L165-L171
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L165-L171

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.norm_multipleIntegralCLM_le (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    ‖multipleIntegralCLM hB n f‖ ≤ Real.sqrt (n.factorial : ℝ) * ‖f‖ := by sorry
