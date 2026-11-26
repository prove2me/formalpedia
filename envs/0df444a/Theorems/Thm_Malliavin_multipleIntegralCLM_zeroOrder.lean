-- Prove2me | Theorems.Thm_Malliavin_multipleIntegralCLM_zeroOrder
-- name    : Malliavin.multipleIntegralCLM_zeroOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:29.054937+00:00
-- url     : https://prove2.me/theorems/c7af0ba4-5c93-46c6-952c-d3abf3bb4f0c
-- title:
--   Malliavin: multiple Integral CLM zero Order
-- statement:
--   Order zero is the constant embedding, hence the selected zeroth homogeneous range.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L217-L228
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L217-L228

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.multipleIntegralCLM_zeroOrder (hB : IsPreBrownianReal B P)
    (f : IteratedKernel 0) :
    (fun ω => multipleIntegralCLM hB 0 f ω) =ᵐ[P]
      fun _ => ∫ t, f t ∂iteratedKernelMeasure 0 := by sorry
