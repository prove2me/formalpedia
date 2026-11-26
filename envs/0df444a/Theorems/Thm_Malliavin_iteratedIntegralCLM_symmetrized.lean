-- Prove2me | Theorems.Thm_Malliavin_iteratedIntegralCLM_symmetrized
-- name    : Malliavin.iteratedIntegralCLM_symmetrized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:48.932258+00:00
-- url     : https://prove2.me/theorems/0bfcc190-ce60-5196-923b-7ade14c63853
-- title:
--   Malliavin: iterated Integral CLM symmetrized
-- statement:
--   On a symmetrized positive-order kernel, `Jₙ₊₁` is the corresponding simplex summand
--   of the global positive tower.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1324-L1330
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1324-L1330

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

theorem Malliavin.iteratedIntegralCLM_symmetrized (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel (n + 1)) :
    iteratedIntegralCLM hB (n + 1)
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) (n + 1) 2 f) =
      IteratedIntegralConstruction.simplexIntegralLI hB n
        (IteratedIntegralConstruction.symmetrizeRestrict (n + 1) f) := by sorry
