-- Prove2me | Theorems.Thm_Malliavin_clarkOcone_comp_pi_wienerIntegral
-- name    : Malliavin.clarkOcone_comp_pi_wienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:38:57.773973+00:00
-- url     : https://prove2.me/theorems/ce2c6302-bb21-593a-93d6-20befc0bb99c
-- title:
--   Malliavin: clark Ocone comp pi wiener Integral
-- statement:
--   **Clark--Ocone for `f (∫ g₁ dB, …, ∫ gₙ dB)`**:
--   `f (∫ g dB) = E[f (∫ g dB)] + C.itoIntegral (Π (∑ᵢ ∂ᵢ f (∫ g dB) gᵢ(t)))`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L335-L347
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L335-L347

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

theorem Malliavin.clarkOcone_comp_pi_wienerIntegral {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (g : Fin n → Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (memLp_comp_pi P hf hK fun i ↦ wienerIntegral C.isPreBrownian (g i)).toLp _ =
      expectationL2
          ((memLp_comp_pi P hf hK fun i ↦ wienerIntegral C.isPreBrownian (g i)).toLp _)
        + C.itoIntegral (predictableProjection 𝓕 (∑ i, tensor (g i)
          ((memLp_fderiv_pi_comp hf hK (fun i ↦ wienerIntegral C.isPreBrownian (g i)) i).toLp
            _))) := by sorry
