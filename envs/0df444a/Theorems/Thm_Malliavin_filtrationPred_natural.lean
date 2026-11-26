-- Prove2me | Theorems.Thm_Malliavin_filtrationPred_natural
-- name    : Malliavin.filtrationPred_natural
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:29:10.580371+00:00
-- url     : https://prove2.me/theorems/3b2f9f0a-7866-40fe-912d-3f12779ac658
-- title:
--   Malliavin: filtration Pred natural
-- statement:
--   For the natural filtration, the strict past is the supremum of the coordinate σ-algebras at
--   strictly earlier times.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L832-L842
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L832-L842

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
variable {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.filtrationPred_natural (hm : ∀ s, StronglyMeasurable (B s)) (t : ℝ≥0) :
    filtrationPred (Filtration.natural B hm) t
      = ⨆ (s : ℝ≥0) (_ : s < t), MeasurableSpace.comap (B s) inferInstance := by sorry
