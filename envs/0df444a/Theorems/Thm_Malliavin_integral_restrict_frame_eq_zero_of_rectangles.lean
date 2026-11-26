-- Prove2me | Theorems.Thm_Malliavin_integral_restrict_frame_eq_zero_of_rectangles
-- name    : Malliavin.integral_restrict_frame_eq_zero_of_rectangles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:24:34.203343+00:00
-- url     : https://prove2.me/theorems/282cc3a3-f20b-4c73-b6e2-92be2af582d6
-- title:
--   Malliavin: integral restrict frame eq zero of rectangles
-- statement:
--   Vanishing on generating rectangles propagates to every predictable set after restriction
--   to a finite time frame.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L247-L303
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L247-L303

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

theorem Malliavin.integral_restrict_frame_eq_zero_of_rectangles
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W))
    (g : PredictableProcessL2 𝓕 P)
    (hrect : ∀ R ∈ predictableRectangle 𝓕,
      ∫ z in R, (g : ℝ≥0 × W → ℝ) z
        ∂nonnegativeLebesgueMeasure.prod P = 0)
    (n : ℕ) (s : Set (ℝ≥0 × W)) (hs : MeasurableSet[𝓕.predictable] s) :
    ∫ z in s, (g : ℝ≥0 × W → ℝ) z
      ∂(nonnegativeLebesgueMeasure.prod P).restrict
        (Set.Ioc 0 ((n : ℝ≥0) + 1) ×ˢ Set.univ) = 0 := by sorry
