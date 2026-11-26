-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_exists_stronglyMeasurable_filtrationPred_ae_eq
-- name    : Malliavin.ClarkOconeFamily.exists_stronglyMeasurable_filtrationPred_ae_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:43.992818+00:00
-- url     : https://prove2.me/theorems/19bb9573-5598-5aa5-a950-67e415fb9a3a
-- title:
--   Clark Ocone Family: exists strongly Measurable filtration Pred ae eq
-- statement:
--   `B t` has a strict-past strongly measurable version.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L1037-L1042
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L1037-L1042

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

theorem Malliavin.ClarkOconeFamily.exists_stronglyMeasurable_filtrationPred_ae_eq
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {t : ℝ≥0} (hat : 0 < t) :
    ∃ Z : W → ℝ, StronglyMeasurable[filtrationPred 𝓕 t] Z ∧ B t =ᵐ[P] Z := by sorry
