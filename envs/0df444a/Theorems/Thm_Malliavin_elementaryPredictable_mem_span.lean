-- Prove2me | Theorems.Thm_Malliavin_elementaryPredictable_mem_span
-- name    : Malliavin.elementaryPredictable_mem_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:22:38.564847+00:00
-- url     : https://prove2.me/theorems/8a437632-74e8-5370-9cb9-0df957985fea
-- title:
--   Malliavin: elementary Predictable mem span
-- statement:
--   The Malliavin construction uses the elementary Predictable mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L219-L225
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L219-L225

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

theorem Malliavin.elementaryPredictable_mem_span
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W)) (a b : ℝ≥0)
    (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryPredictable 𝓕 a b Z ∈ elementaryPredictableSpan (P := P) 𝓕 := by sorry
