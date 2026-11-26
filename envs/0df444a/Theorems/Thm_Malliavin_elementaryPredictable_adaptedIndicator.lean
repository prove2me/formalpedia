-- Prove2me | Theorems.Thm_Malliavin_elementaryPredictable_adaptedIndicator
-- name    : Malliavin.elementaryPredictable_adaptedIndicator
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:32:18.653156+00:00
-- url     : https://prove2.me/theorems/2cc5bc64-7c45-4de7-9587-320f6d36ee27
-- title:
--   Malliavin: elementary Predictable adapted Indicator
-- statement:
--   An elementary process with an event-indicator coefficient is the indicator of its
--   predictable rectangle.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L150-L179
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L150-L179

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
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.elementaryPredictable_adaptedIndicator
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    {F : Set W} (hF : MeasurableSet[𝓕 a] F) :
    (elementaryPredictable (P := P) 𝓕 a b (adaptedIndicator (P := P) 𝓕 a hF) :
        TimeProcessL2 P) =
      indicatorConstLp (μ := nonnegativeLebesgueMeasure.prod P) 2
        (measurableSet_Ioc.prod (𝓕.le a F hF))
        (by
          rw [Measure.prod_prod (μ := nonnegativeLebesgueMeasure) (ν := P)]
          exact ENNReal.mul_ne_top
            (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (measure_ne_top P F))
        (1 : ℝ) := by sorry
