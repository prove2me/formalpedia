-- Prove2me | Theorems.Thm_Malliavin_integral_rectangle_eq_zero_of_orthogonal
-- name    : Malliavin.integral_rectangle_eq_zero_of_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:22:48.345151+00:00
-- url     : https://prove2.me/theorems/9ede61b0-e4fb-5cf5-a4d6-8ce252b10991
-- title:
--   Malliavin: integral rectangle eq zero of orthogonal
-- statement:
--   The Malliavin construction uses the integral rectangle eq zero of orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L228-L242
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L228-L242

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

theorem Malliavin.integral_rectangle_eq_zero_of_orthogonal
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W))
    (g : PredictableProcessL2 𝓕 P)
    (horth : ∀ U : PredictableProcessL2 𝓕 P,
      U ∈ elementaryPredictableSpan (P := P) 𝓕 → ⟪U, g⟫_ℝ = 0) :
    ∀ R ∈ predictableRectangle 𝓕,
      ∫ z in R, (g : ℝ≥0 × W → ℝ) z
        ∂nonnegativeLebesgueMeasure.prod P = 0 := by sorry
