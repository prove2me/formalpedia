-- Prove2me | Theorems.Thm_Malliavin_generateFrom_predictableRectangle
-- name    : Malliavin.generateFrom_predictableRectangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:22:20.191005+00:00
-- url     : https://prove2.me/theorems/fbaf0457-b200-4a9c-8719-9484f57fa207
-- title:
--   Malliavin: generate From predictable Rectangle
-- statement:
--   The Malliavin construction uses the generate From predictable Rectangle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L98-L128
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L98-L128

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_PredictableDensity
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.generateFrom_predictableRectangle
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    MeasurableSpace.generateFrom (predictableRectangle 𝓕) = 𝓕.predictable := by sorry
