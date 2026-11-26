-- Prove2me | Theorems.Thm_Malliavin_clarkOcone_wickExp
-- name    : Malliavin.clarkOcone_wickExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:38:26.954795+00:00
-- url     : https://prove2.me/theorems/775673a2-3a2f-5e85-80d0-dd67c876f722
-- title:
--   Malliavin: clark Ocone wick Exp
-- statement:
--   **Clark--Ocone for the Wick exponential** `exp (B T - T / 2)`:
--   `exp (B T - T/2) = E[exp (B T - T/2)] + C.itoIntegral (Π (exp (B T - T/2) 1_{(0, T]}))`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L251-L270
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L251-L270

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

theorem Malliavin.clarkOcone_wickExp {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (T : ℝ≥0) :
    (memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _ =
      expectationL2 ((memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _)
        + C.itoIntegral (predictableProjection 𝓕 (tensor (intervalIndicator T)
          ((memLp_wickExp_brownian C.coordinate C.coordinate_apply T).toLp _))) := by sorry
