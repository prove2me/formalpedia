-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_ofHermiteMultipleIntegralIdentity_isBrownianOnElementary
-- name    : Malliavin.ClarkOconeFamily.ofHermiteMultipleIntegralIdentity_isBrownianOnElementary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:21.674558+00:00
-- url     : https://prove2.me/theorems/8ebe4368-bb20-4887-8564-6785f836770f
-- title:
--   Clark Ocone Family: of Hermite Multiple Integral Identity is Brownian On Elementary
-- statement:
--   The identity-based family has the genuine Brownian value on elementary adapted processes.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermiteClarkOcone.lean#L120-L132
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermiteClarkOcone.lean#L120-L132

import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
import Definitions.Def_Malliavin_PastCylinderDensity
import Definitions.Def_Malliavin_BrownianHermiteClarkOcone
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
open BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.ClarkOconeFamily.ofHermiteMultipleIntegralIdentity_isBrownianOnElementary
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    (ClarkOconeFamily.ofHermiteMultipleIntegralIdentity
      hB coordinate coordinate_apply generated hsm hnat hid
      ).IsBrownianOnElementary := by sorry
