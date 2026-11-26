-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_IsBrownianOnElementary_itoIntegral_eq
-- name    : Malliavin.ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:32:50.859718+00:00
-- url     : https://prove2.me/theorems/67b6220a-9ce8-542b-b599-fae3b86d28c7
-- title:
--   Is Brownian On Elementary: ito Integral eq
-- statement:
--   The elementary compatibility predicate determines the designated integral uniquely on all
--   predictable `L²`, because the elementary span is dense.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L426-L441
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L426-L441

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
set_option maxHeartbeats 220000

theorem Malliavin.ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_eq
    {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {C D : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnElementary) (hD : D.IsBrownianOnElementary) :
    C.itoIntegral = D.itoIntegral := by sorry
