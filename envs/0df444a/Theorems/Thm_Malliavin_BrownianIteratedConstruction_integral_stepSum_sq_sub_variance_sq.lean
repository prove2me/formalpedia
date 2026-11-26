-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_stepSum_sq_sub_variance_sq
-- name    : Malliavin.BrownianIteratedConstruction.integral_stepSum_sq_sub_variance_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:29:12.7624+00:00
-- url     : https://prove2.me/theorems/c6dcfa8a-702a-4acd-b8de-63ea05fd3b1c
-- title:
--   Brownian Iterated Construction: integral step Sum sq sub variance sq
-- statement:
--   The centered square of a finite Brownian step sum has second moment twice the squared
--   variance.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L81-L97
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L81-L97

import Definitions.Def_Malliavin_GaussianHermite
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Definitions.Def_Malliavin_BrownianWickIsometry
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.integral_stepSum_sq_sub_variance_sq
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    (∫ w, (stepSum B v w ^ 2 - ‖stepToLp v‖ ^ 2) ^ 2 ∂P) =
      2 * (‖stepToLp v‖ ^ 2) ^ 2 := by sorry
