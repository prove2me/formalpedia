-- Prove2me | Theorems.Thm_Malliavin_clarkOcone_comp_wienerIntegral
-- name    : Malliavin.clarkOcone_comp_wienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:39:00.330056+00:00
-- url     : https://prove2.me/theorems/f3e619df-2aeb-46d7-9bca-5144ab135a61
-- title:
--   Malliavin: clark Ocone comp wiener Integral
-- statement:
--   **Clark--Ocone for `φ (∫ g dB)`**:
--   `φ (∫ g dB) = E[φ (∫ g dB)] + C.itoIntegral (Π (φ' (∫ g dB) g(t)))`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L298-L308
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L298-L308

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

theorem Malliavin.clarkOcone_comp_wienerIntegral {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ContDiff ℝ 1 φ)
    (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (memLp_comp_of_deriv_le P hφ hK (wienerIntegral C.isPreBrownian g)).toLp _ =
      expectationL2 ((memLp_comp_of_deriv_le P hφ hK (wienerIntegral C.isPreBrownian g)).toLp _)
        + C.itoIntegral (predictableProjection 𝓕
          (tensor g ((memLp_deriv_comp hφ hK (wienerIntegral C.isPreBrownian g)).toLp _))) := by sorry
