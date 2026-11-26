-- Prove2me | Theorems.Thm_Malliavin_naturalItoIntegral_deterministic_intervalIndicator
-- name    : Malliavin.naturalItoIntegral_deterministic_intervalIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:50:45.245861+00:00
-- url     : https://prove2.me/theorems/3a788715-864e-5e65-901e-e915edd81ce5
-- title:
--   Malliavin: natural Ito Integral deterministic interval Indicator
-- statement:
--   On `1_(0,t]`, the constructed Itô integral is the Brownian coordinate `B_t` in `L²(P)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L188-L195
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L188-L195

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
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

theorem Malliavin.naturalItoIntegral_deterministic_intervalIndicator
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (t : ℝ≥0) :
    naturalItoIntegral hB hsm hnat
        (deterministicPredictableEmbedding 𝓅 (intervalIndicator t)) =
      brownianLp hB t := by sorry
