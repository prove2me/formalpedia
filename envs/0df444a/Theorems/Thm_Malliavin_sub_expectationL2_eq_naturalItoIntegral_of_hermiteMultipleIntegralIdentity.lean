-- Prove2me | Theorems.Thm_Malliavin_sub_expectationL2_eq_naturalItoIntegral_of_hermiteMultipleIntegralIdentity
-- name    : Malliavin.sub_expectationL2_eq_naturalItoIntegral_of_hermiteMultipleIntegralIdentity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:25.572418+00:00
-- url     : https://prove2.me/theorems/60dbce2a-20e3-40be-aa21-347dfe0c669f
-- title:
--   Malliavin: sub expectation L2 eq natural Ito Integral of hermite Multiple Integral Identity
-- statement:
--   Centered form of Clark--Ocone under the Hermite/multiple-integral identity.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermiteClarkOcone.lean#L80-L99
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermiteClarkOcone.lean#L80-L99

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

theorem Malliavin.sub_expectationL2_eq_naturalItoIntegral_of_hermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB)
    (F : D12 P) :
    F.1 - expectationL2 F.1 = naturalItoIntegral hB hsm hnat
      (predictableProjection filtration
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) := by sorry
