-- Prove2me | Theorems.Thm_Malliavin_naturalItoIntegral_elementaryPredictable
-- name    : Malliavin.naturalItoIntegral_elementaryPredictable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:40:34.885181+00:00
-- url     : https://prove2.me/theorems/6068aec9-e193-45f1-a723-e51b2fb482bd
-- title:
--   Malliavin: natural Ito Integral elementary Predictable
-- statement:
--   On an elementary adapted process, the constructed integral is `Z (B_b - B_a)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConstruction.lean#L362-L374
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConstruction.lean#L362-L374

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
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.naturalItoIntegral_elementaryPredictable
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    naturalItoIntegral hB hsm hnat (elementaryPredictable 𝓕 a b Z) =
      elementaryBrownianValue hB hsm hnat hab Z := by sorry
