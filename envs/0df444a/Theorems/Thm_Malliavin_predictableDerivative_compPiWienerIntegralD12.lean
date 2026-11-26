-- Prove2me | Theorems.Thm_Malliavin_predictableDerivative_compPiWienerIntegralD12
-- name    : Malliavin.predictableDerivative_compPiWienerIntegralD12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:36:59.849206+00:00
-- url     : https://prove2.me/theorems/77d05671-8370-5baa-bdf6-6b349bbc1100
-- title:
--   Malliavin: predictable Derivative comp Pi Wiener Integral D12
-- statement:
--   **The Clark--Ocone integrand of `f (∫ g₁ dB, …, ∫ gₙ dB)`** is the predictable projection of
--   `∑ᵢ ∂ᵢ f (∫ g dB) gᵢ(t)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L320-L331
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L320-L331

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

theorem Malliavin.predictableDerivative_compPiWienerIntegralD12 {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (g : Fin n → Lp ℝ 2 nonnegativeLebesgueMeasure) :
    predictableDerivative C (compPiWienerIntegralD12 C.isPreBrownian C.coordinate
        C.coordinate_apply C.generated hf hK g) =
      predictableProjection 𝓕 (∑ i, tensor (g i)
        ((memLp_fderiv_pi_comp hf hK (fun i ↦ wienerIntegral C.isPreBrownian (g i)) i).toLp
          _)) := by sorry
