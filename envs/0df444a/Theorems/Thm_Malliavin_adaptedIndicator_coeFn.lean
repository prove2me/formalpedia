-- Prove2me | Theorems.Thm_Malliavin_adaptedIndicator_coeFn
-- name    : Malliavin.adaptedIndicator_coeFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:17:25.855627+00:00
-- url     : https://prove2.me/theorems/fa34993e-da31-521f-bb61-e86bf31d0900
-- title:
--   Malliavin: adapted Indicator coe Fn
-- statement:
--   The Malliavin construction uses the adapted Indicator coe Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L139-L145
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L139-L145

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

theorem Malliavin.adaptedIndicator_coeFn
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a : ℝ≥0)
    {F : Set W} (hF : MeasurableSet[𝓕 a] F) :
    (adaptedIndicator (P := P) 𝓕 a hF : W → ℝ) =ᵐ[P]
      F.indicator (fun _ ↦ (1 : ℝ)) := by sorry
