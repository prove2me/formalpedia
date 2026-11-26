-- Prove2me | Theorems.Thm_Malliavin_inner_iteratedIntegralCLM_ne
-- name    : Malliavin.inner_iteratedIntegralCLM_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:52:37.928797+00:00
-- url     : https://prove2.me/theorems/787d12b9-2017-4a52-9489-19862f824bab
-- title:
--   Malliavin: inner iterated Integral CLM ne
-- statement:
--   Different orders in the selected tower are orthogonal in `L²(P)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1353-L1356
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L1353-L1356

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

theorem Malliavin.inner_iteratedIntegralCLM_ne (hB : IsPreBrownianReal B P) {m n : ℕ}
    (hmn : m ≠ n) (f : IteratedKernel m) (g : IteratedKernel n) :
    inner ℝ (iteratedIntegralCLM hB m f) (iteratedIntegralCLM hB n g) = 0 := by sorry
