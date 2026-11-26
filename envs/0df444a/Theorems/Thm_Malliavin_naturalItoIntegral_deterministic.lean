-- Prove2me | Theorems.Thm_Malliavin_naturalItoIntegral_deterministic
-- name    : Malliavin.naturalItoIntegral_deterministic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:45:23.997423+00:00
-- url     : https://prove2.me/theorems/27a3661a-4594-58ee-8b01-8aa15650cad9
-- title:
--   Malliavin: natural Ito Integral deterministic
-- statement:
--   The constructed Itô integral agrees with the Wiener integral on every deterministic
--   square-integrable time integrand.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L161-L169
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L161-L169

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

theorem Malliavin.naturalItoIntegral_deterministic
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    naturalItoIntegral hB hsm hnat (deterministicPredictableEmbedding 𝓅 f) =
      wienerIntegral hB f := by sorry
