-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_elementaryIntegralValue_eq
-- name    : Malliavin.ClarkOconeFamily.elementaryIntegralValue_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:22:55.065512+00:00
-- url     : https://prove2.me/theorems/31895e42-ca5c-5818-90c8-ccc714bd23a3
-- title:
--   Clark Ocone Family: elementary Integral Value eq
-- statement:
--   The one-step Brownian target does not depend on which `ClarkOconeFamily` supplies the
--   Brownian and natural-filtration proofs.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L414-L421
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L414-L421

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_PredictableDensity
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]

theorem Malliavin.ClarkOconeFamily.elementaryIntegralValue_eq
    {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C D : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    C.elementaryIntegralValue hab Z = D.elementaryIntegralValue hab Z := by sorry
