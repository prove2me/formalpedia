-- Prove2me | Theorems.Thm_Malliavin_inner_iteratedIntegralCLM
-- name    : Malliavin.inner_iteratedIntegralCLM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:52.880568+00:00
-- url     : https://prove2.me/theorems/80c70a2a-9a68-54ff-8eeb-85955a97bab7
-- title:
--   Malliavin: inner iterated Integral CLM
-- statement:
--   The polarized simplex isometry for two kernels of the same order.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1333-L1337
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1333-L1337

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

theorem Malliavin.inner_iteratedIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ)
    (f g : IteratedKernel n) :
    inner ℝ (iteratedIntegralCLM hB n f) (iteratedIntegralCLM hB n g) =
      ∫ t in simplex ℝ≥0 n, inner ℝ (f t) (g t) ∂iteratedKernelMeasure n := by sorry
