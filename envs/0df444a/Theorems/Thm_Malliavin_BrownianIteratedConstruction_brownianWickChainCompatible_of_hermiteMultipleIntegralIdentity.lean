-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickChainCompatible_of_hermiteMultipleIntegralIdentity
-- name    : Malliavin.BrownianIteratedConstruction.brownianWickChainCompatible_of_hermiteMultipleIntegralIdentity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:09:53.996551+00:00
-- url     : https://prove2.me/theorems/256d9f1c-cb3f-53d1-978a-46f73888e5a8
-- title:
--   Brownian Iterated Construction: brownian Wick Chain Compatible of hermite Multiple Integral Identity
-- statement:
--   The Hermite/multiple-integral identity supplies Wick-chain compatibility at every order.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermiteMultipleIntegral.lean#L69-L75
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermiteMultipleIntegral.lean#L69-L75

import Definitions.Def_Malliavin_BrownianPurePowerIntegral
import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.BrownianIteratedConstruction.brownianWickChainCompatible_of_hermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    BrownianWickChainCompatible hB := by sorry
