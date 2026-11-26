-- Prove2me | Theorems.Thm_Malliavin_integral_multipleIntegralCLM
-- name    : Malliavin.integral_multipleIntegralCLM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:08:00.077379+00:00
-- url     : https://prove2.me/theorems/9b3a2351-9931-547c-b97a-0763cb5ce376
-- title:
--   Malliavin: integral multiple Integral CLM
-- statement:
--   Positive-order selected multiple operators have centered output.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L181-L197
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L181-L197

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.integral_multipleIntegralCLM (hB : IsPreBrownianReal B P) {n : ℕ} (hn : 0 < n)
    (f : IteratedKernel n) :
    ∫ ω, multipleIntegralCLM hB n f ω ∂P = 0 := by sorry
