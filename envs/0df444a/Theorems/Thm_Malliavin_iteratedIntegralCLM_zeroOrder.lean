-- Prove2me | Theorems.Thm_Malliavin_iteratedIntegralCLM_zeroOrder
-- name    : Malliavin.iteratedIntegralCLM_zeroOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:53.320798+00:00
-- url     : https://prove2.me/theorems/01af4942-88a0-58a8-919a-64ee527fc40b
-- title:
--   Malliavin: iterated Integral CLM zero Order
-- statement:
--   `J₀` identifies the one-dimensional zeroth kernel space with constant random variables.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1346-L1350
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1346-L1350

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral
set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
open ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace lp
variable {Ω' : Type*} [mΩ' : MeasurableSpace Ω'] {P : Measure Ω'}
  {B : ℝ≥0 → Ω' → ℝ}

theorem Malliavin.iteratedIntegralCLM_zeroOrder (hB : IsPreBrownianReal B P)
    (f : IteratedKernel 0) :
    (fun ω => iteratedIntegralCLM hB 0 f ω) =ᵐ[P]
      fun _ => ∫ t, f t ∂iteratedKernelMeasure 0 := by sorry
