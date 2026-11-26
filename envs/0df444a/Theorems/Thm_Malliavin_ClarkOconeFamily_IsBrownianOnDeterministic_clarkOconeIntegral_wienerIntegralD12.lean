-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_IsBrownianOnDeterministic_clarkOconeIntegral_wienerIntegralD12
-- name    : Malliavin.ClarkOconeFamily.IsBrownianOnDeterministic.clarkOconeIntegral_wienerIntegralD12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:38:28.892298+00:00
-- url     : https://prove2.me/theorems/b1d28293-0ce2-4a16-97ea-61632ac2d160
-- title:
--   Is Brownian On Deterministic: clark Ocone Integral wiener Integral D12
-- statement:
--   **Clark--Ocone is tautological on the first chaos**: for a family Brownian on deterministic
--   integrands, the Clark--Ocone integral of `∫ g dB` is `∫ g dB` itself.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L123-L132
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L123-L132

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}

theorem Malliavin.ClarkOconeFamily.IsBrownianOnDeterministic.clarkOconeIntegral_wienerIntegralD12
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnDeterministic) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    clarkOconeIntegral C
        (wienerIntegralD12 C.isPreBrownian C.coordinate C.coordinate_apply C.generated g) =
      wienerIntegral C.isPreBrownian g := by sorry
