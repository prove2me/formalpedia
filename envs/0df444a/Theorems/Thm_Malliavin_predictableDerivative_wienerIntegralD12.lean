-- Prove2me | Theorems.Thm_Malliavin_predictableDerivative_wienerIntegralD12
-- name    : Malliavin.predictableDerivative_wienerIntegralD12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:36:25.425377+00:00
-- url     : https://prove2.me/theorems/8de6e571-5041-4a13-8f1a-6b17ea2e692c
-- title:
--   Malliavin: predictable Derivative wiener Integral D12
-- statement:
--   **The Clark--Ocone integrand of `∫ g dB` is `g`**: the predictable derivative of a first-chaos
--   functional is its deterministic kernel.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L111-L119
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L111-L119

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

theorem Malliavin.predictableDerivative_wienerIntegralD12 {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    predictableDerivative C
        (wienerIntegralD12 C.isPreBrownian C.coordinate C.coordinate_apply C.generated g) =
      deterministicPredictableEmbedding 𝓕 g := by sorry
