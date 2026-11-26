-- Prove2me | Theorems.Thm_Malliavin_integral_set_eq_zero_of_rectangles
-- name    : Malliavin.integral_set_eq_zero_of_rectangles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:17:43.229668+00:00
-- url     : https://prove2.me/theorems/ff304be0-4ead-5750-8bd9-4c08edfc2a95
-- title:
--   Malliavin: integral set eq zero of rectangles
-- statement:
--   Vanishing on the generating predictable rectangles implies vanishing on every
--   finite-measure predictable set.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L308-L373
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L308-L373

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

theorem Malliavin.integral_set_eq_zero_of_rectangles
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W))
    (g : PredictableProcessL2 𝓕 P)
    (hrect : ∀ R ∈ predictableRectangle 𝓕,
      ∫ z in R, (g : ℝ≥0 × W → ℝ) z
        ∂nonnegativeLebesgueMeasure.prod P = 0)
    (s : Set (ℝ≥0 × W)) (hs : MeasurableSet[𝓕.predictable] s)
    (hμs : (nonnegativeLebesgueMeasure.prod P) s < ∞) :
    ∫ z in s, (g : ℝ≥0 × W → ℝ) z
      ∂nonnegativeLebesgueMeasure.prod P = 0 := by sorry
