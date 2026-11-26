-- Prove2me | Theorems.Thm_Malliavin_predictableDerivative_cylinderGrowthD12
-- name    : Malliavin.predictableDerivative_cylinderGrowthD12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:36:33.128651+00:00
-- url     : https://prove2.me/theorems/3024e19c-237a-4d90-9be1-79a79eca68f2
-- title:
--   Malliavin: predictable Derivative cylinder Growth D12
-- statement:
--   **The Clark--Ocone integrand of `f (B t₁, …, B tₙ)`** is the predictable projection of
--   `∑ᵢ ∂ᵢ f (B) 1_{(0, tᵢ]}(t)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L221-L232
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L221-L232

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

theorem Malliavin.predictableDerivative_cylinderGrowthD12 {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {K : ℝ} (hK : 0 ≤ K) (hfg : ∀ y, |f y| ≤ K * (1 + ‖y‖) ^ k)
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ K * (1 + ‖y‖) ^ k) (t : Fin n → ℝ≥0) :
    predictableDerivative C
        (cylinderGrowthD12 C.coordinate C.coordinate_apply hf hK hfg hfg' t) =
      predictableProjection 𝓕 (∑ i, tensor (intervalIndicator (t i))
        (cylinderPartialGrowth C.coordinate C.coordinate_apply hf hK hfg' t i)) := by sorry
