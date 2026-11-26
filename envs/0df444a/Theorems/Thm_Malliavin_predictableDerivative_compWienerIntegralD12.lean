-- Prove2me | Theorems.Thm_Malliavin_predictableDerivative_compWienerIntegralD12
-- name    : Malliavin.predictableDerivative_compWienerIntegralD12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:36:35.547935+00:00
-- url     : https://prove2.me/theorems/e6d43d69-bb7f-4807-a486-2fff5959e16a
-- title:
--   Malliavin: predictable Derivative comp Wiener Integral D12
-- statement:
--   **The Clark--Ocone integrand of `φ (∫ g dB)`** is the predictable projection of
--   `φ' (∫ g dB) g(t)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L284-L294
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L284-L294

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

theorem Malliavin.predictableDerivative_compWienerIntegralD12 {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ContDiff ℝ 1 φ)
    (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    predictableDerivative C (compWienerIntegralD12 C.isPreBrownian C.coordinate
        C.coordinate_apply C.generated hφ hK g) =
      predictableProjection 𝓕
        (tensor g ((memLp_deriv_comp hφ hK (wienerIntegral C.isPreBrownian g)).toLp _)) := by sorry
