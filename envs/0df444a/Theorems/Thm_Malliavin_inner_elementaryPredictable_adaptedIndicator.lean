-- Prove2me | Theorems.Thm_Malliavin_inner_elementaryPredictable_adaptedIndicator
-- name    : Malliavin.inner_elementaryPredictable_adaptedIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:22:23.94424+00:00
-- url     : https://prove2.me/theorems/28951d54-20b1-52a3-bfbb-6cc47b403c53
-- title:
--   Malliavin: inner elementary Predictable adapted Indicator
-- statement:
--   The Malliavin construction uses the inner elementary Predictable adapted Indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L182-L207
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L182-L207

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
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]

theorem Malliavin.inner_elementaryPredictable_adaptedIndicator
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    {F : Set W} (hF : MeasurableSet[𝓕 a] F)
    (g : PredictableProcessL2 𝓕 P) :
    ⟪elementaryPredictable 𝓕 a b (adaptedIndicator (P := P) 𝓕 a hF), g⟫_ℝ =
      ∫ z in Set.Ioc a b ×ˢ F, (g : ℝ≥0 × W → ℝ) z
        ∂nonnegativeLebesgueMeasure.prod P := by sorry
