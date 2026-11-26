-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_inner_elementaryIntegralValue_eq_inner_elementaryPredictable
-- name    : Malliavin.ClarkOconeFamily.inner_elementaryIntegralValue_eq_inner_elementaryPredictable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:41:44.047888+00:00
-- url     : https://prove2.me/theorems/adf542e1-72a1-4890-98ab-beadf1500349
-- title:
--   Clark Ocone Family: inner elementary Integral Value eq inner elementary Predictable
-- statement:
--   A family's elementary Brownian values satisfy the arbitrary-interval cross Itô identity.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConstruction.lean#L198-L208
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConstruction.lean#L198-L208

import Definitions.Def_Malliavin_ElementaryIto
import Definitions.Def_Malliavin_PredictableDensity
import Definitions.Def_Malliavin_ItoConstruction
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

theorem Malliavin.ClarkOconeFamily.inner_elementaryIntegralValue_eq_inner_elementaryPredictable
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hcd : c ≤ d)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (C.elementaryIntegralValue hab Z) (C.elementaryIntegralValue hcd Y) =
      inner ℝ (elementaryPredictable 𝓕 a b Z)
        (elementaryPredictable 𝓕 c d Y) := by sorry
