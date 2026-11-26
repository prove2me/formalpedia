-- Prove2me | Theorems.Thm_Malliavin_integral_iteratedIntegralCLM
-- name    : Malliavin.integral_iteratedIntegralCLM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:50.759343+00:00
-- url     : https://prove2.me/theorems/a5ad7c9f-6307-5b28-9516-c0f225cbb31f
-- title:
--   Malliavin: integral iterated Integral CLM
-- statement:
--   Positive-order operators in the selected family have expectation zero.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1340-L1343
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1340-L1343

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

theorem Malliavin.integral_iteratedIntegralCLM (hB : IsPreBrownianReal B P) {n : ℕ} (hn : 0 < n)
    (f : IteratedKernel n) :
    ∫ ω, iteratedIntegralCLM hB n f ω ∂P = 0 := by sorry
