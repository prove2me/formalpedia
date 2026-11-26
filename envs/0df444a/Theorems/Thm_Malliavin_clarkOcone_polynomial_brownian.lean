-- Prove2me | Theorems.Thm_Malliavin_clarkOcone_polynomial_brownian
-- name    : Malliavin.clarkOcone_polynomial_brownian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:36:05.726143+00:00
-- url     : https://prove2.me/theorems/7affee2a-a8ad-551a-abd1-a121456e64c5
-- title:
--   Malliavin: clark Ocone polynomial brownian
-- statement:
--   **Clark--Ocone for polynomials of a Brownian coordinate**:
--   `p (B T) = E[p (B T)] + C.itoIntegral (Π (p' (B T) 1_{(0, T]}))` for every real polynomial `p`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L197-L207
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L197-L207

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

theorem Malliavin.clarkOcone_polynomial_brownian {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (p : Polynomial ℝ) (T : ℝ≥0) :
    (memLp_polynomial_brownian C.coordinate C.coordinate_apply p T).toLp _ =
      expectationL2 ((memLp_polynomial_brownian C.coordinate C.coordinate_apply p T).toLp _)
        + C.itoIntegral (predictableProjection 𝓕 (tensor (intervalIndicator T)
          ((memLp_polynomial_derivative_brownian C.coordinate C.coordinate_apply p T).toLp
            _))) := by sorry
