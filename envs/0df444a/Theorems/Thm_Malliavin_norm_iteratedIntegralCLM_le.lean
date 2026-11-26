-- Prove2me | Theorems.Thm_Malliavin_norm_iteratedIntegralCLM_le
-- name    : Malliavin.norm_iteratedIntegralCLM_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:59:11.900423+00:00
-- url     : https://prove2.me/theorems/c9e1ab26-fb8f-56a5-96a3-73c9e498d892
-- title:
--   Malliavin: norm iterated Integral CLM le
-- statement:
--   The full-product-domain operator `Jₙ` is a contraction.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1359-L1362
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1359-L1362

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

theorem Malliavin.norm_iteratedIntegralCLM_le (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    ‖iteratedIntegralCLM hB n f‖ ≤ ‖f‖ := by sorry
