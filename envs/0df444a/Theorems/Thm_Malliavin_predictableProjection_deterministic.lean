-- Prove2me | Theorems.Thm_Malliavin_predictableProjection_deterministic
-- name    : Malliavin.predictableProjection_deterministic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:35:55.778922+00:00
-- url     : https://prove2.me/theorems/04126d03-f19a-5f35-b598-3077307fef62
-- title:
--   Malliavin: predictable Projection deterministic
-- statement:
--   The predictable projection fixes deterministic integrands.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L65-L73
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L65-L73

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
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.predictableProjection_deterministic (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    predictableProjection (P := P) 𝓕 (deterministicTimeEmbedding g) =
      deterministicPredictableEmbedding 𝓕 g := by sorry
