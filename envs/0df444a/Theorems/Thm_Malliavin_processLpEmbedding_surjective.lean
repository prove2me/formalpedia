-- Prove2me | Theorems.Thm_Malliavin_processLpEmbedding_surjective
-- name    : Malliavin.processLpEmbedding_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:49:15.872798+00:00
-- url     : https://prove2.me/theorems/3567af41-739c-5aee-8153-0689b1366f86
-- title:
--   Malliavin: process Lp Embedding surjective
-- statement:
--   If the process sigma-algebra is ambient, its `L²` embedding is onto.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L464-L485
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L464-L485

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

theorem Malliavin.processLpEmbedding_surjective
    (P : Measure Ω') (B : ℝ≥0 → Ω' → ℝ) (hmeas : ∀ t, Measurable (B t))
    (hgen : processMeasurableSpace B = mΩ') :
    Function.Surjective (processLpEmbedding P B hmeas) := by sorry
