-- Prove2me | Theorems.Thm_Malliavin_clarkOcone_cylinder_growth
-- name    : Malliavin.clarkOcone_cylinder_growth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:38:59.144799+00:00
-- url     : https://prove2.me/theorems/3ed6c701-999c-494d-b7da-87c07cbadee6
-- title:
--   Malliavin: clark Ocone cylinder growth
-- statement:
--   **Clark--Ocone for polynomial-growth functions of Brownian coordinates**:
--   `f (B t₁, …, B tₙ) = E[f (B)] + C.itoIntegral (Π (∑ᵢ ∂ᵢ f (B) 1_{(0, tᵢ]}))`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L236-L247
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L236-L247

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

theorem Malliavin.clarkOcone_cylinder_growth {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {K : ℝ} (hK : 0 ≤ K) (hfg : ∀ y, |f y| ≤ K * (1 + ‖y‖) ^ k)
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ K * (1 + ‖y‖) ^ k) (t : Fin n → ℝ≥0) :
    (memLp_cylinder_growth_brownian C.coordinate C.coordinate_apply hf hK hfg t).toLp _ =
      expectationL2
          ((memLp_cylinder_growth_brownian C.coordinate C.coordinate_apply hf hK hfg t).toLp _)
        + C.itoIntegral (predictableProjection 𝓕 (∑ i, tensor (intervalIndicator (t i))
          (cylinderPartialGrowth C.coordinate C.coordinate_apply hf hK hfg' t i))) := by sorry
