-- Prove2me | Theorems.Thm_Malliavin_stronglyMeasurable_timeSection_of_predictable
-- name    : Malliavin.stronglyMeasurable_timeSection_of_predictable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:29:54.32919+00:00
-- url     : https://prove2.me/theorems/7dc3f95a-de0f-5461-8179-7f7327e9c22d
-- title:
--   Malliavin: strongly Measurable time Section of predictable
-- statement:
--   Sections of predictable strongly measurable processes are `𝓕 t`-strongly measurable, for
--   every `t`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L286-L289
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L286-L289

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W]

theorem Malliavin.stronglyMeasurable_timeSection_of_predictable {V : ℝ≥0 × W → ℝ}
    (hV : StronglyMeasurable[𝓕.predictable] V) (t : ℝ≥0) :
    StronglyMeasurable[𝓕 t] fun ω ↦ V (t, ω) := by sorry
