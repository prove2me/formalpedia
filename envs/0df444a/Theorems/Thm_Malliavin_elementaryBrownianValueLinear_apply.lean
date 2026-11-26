-- Prove2me | Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
-- name    : Malliavin.elementaryBrownianValueLinear_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:14:54.047097+00:00
-- url     : https://prove2.me/theorems/adc91860-f981-4da3-809f-a54c29d79b6a
-- title:
--   Malliavin: elementary Brownian Value Linear apply
-- statement:
--   The fixed-interval linear map evaluates to the elementary Brownian value.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L446-L453
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L446-L453

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_ElementaryIto
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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.elementaryBrownianValueLinear_apply
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryBrownianValueLinear hB hsm hnat hab Z =
      elementaryBrownianValue hB hsm hnat hab Z := by sorry

attribute [defeq] Malliavin.elementaryBrownianValueLinear_apply
