-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_deterministicIntegral_apply
-- name    : Malliavin.ClarkOconeFamily.deterministicIntegral_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:14:17.666456+00:00
-- url     : https://prove2.me/theorems/5bdf930f-cc6e-4581-8acb-128e13a3c885
-- title:
--   Clark Ocone Family: deterministic Integral apply
-- statement:
--   The Clark Ocone Family construction uses the deterministic Integral apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L705-L709
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L705-L709

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.ClarkOconeFamily.deterministicIntegral_apply
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    C.deterministicIntegral f =
      C.itoIntegral (deterministicPredictableEmbedding 𝓕 f) := by sorry
