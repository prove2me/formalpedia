-- Prove2me | Theorems.Thm_Malliavin_elementaryBrownianCoefficientCLM_apply
-- name    : Malliavin.elementaryBrownianCoefficientCLM_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:44:33.834157+00:00
-- url     : https://prove2.me/theorems/af0d4b37-61a7-4839-9d76-783d1e7a12d9
-- title:
--   Malliavin: elementary Brownian Coefficient CLM apply
-- statement:
--   The Malliavin construction uses the elementary Brownian Coefficient CLM apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalClarkOcone.lean#L357-L366
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalClarkOcone.lean#L357-L366

import Definitions.Def_Malliavin_KernelIdentification
import Definitions.Def_Malliavin_NaturalClarkOcone
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.elementaryBrownianCoefficientCLM_apply
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryBrownianCoefficientCLM hB hsm hnat hab Z =
      elementaryBrownianValue hB hsm hnat hab Z := by sorry
