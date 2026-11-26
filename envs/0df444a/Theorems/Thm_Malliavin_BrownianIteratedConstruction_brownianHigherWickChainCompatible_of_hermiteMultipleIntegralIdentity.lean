-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianHigherWickChainCompatible_of_hermiteMultipleIntegralIdentity
-- name    : Malliavin.BrownianIteratedConstruction.brownianHigherWickChainCompatible_of_hermiteMultipleIntegralIdentity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:20.032554+00:00
-- url     : https://prove2.me/theorems/203ef1c8-5887-43e1-b49b-94adf3bfd2d7
-- title:
--   Brownian Iterated Construction: brownian Higher Wick Chain Compatible of hermite Multiple Integral Identity
-- statement:
--   The Hermite/multiple-integral identity puts every higher Wick power in the ordered-chain
--   closure.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermiteMultipleIntegral.lean#L57-L65
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermiteMultipleIntegral.lean#L57-L65

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

theorem Malliavin.BrownianIteratedConstruction.brownianHigherWickChainCompatible_of_hermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    BrownianHigherWickChainCompatible hB := by sorry
