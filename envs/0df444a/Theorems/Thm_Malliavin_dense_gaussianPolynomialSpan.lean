-- Prove2me | Theorems.Thm_Malliavin_dense_gaussianPolynomialSpan
-- name    : Malliavin.dense_gaussianPolynomialSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:52:48.59085+00:00
-- url     : https://prove2.me/theorems/e63e3897-0352-53f4-8562-e3b262c5fcb5
-- title:
--   Malliavin: dense gaussian Polynomial Span
-- statement:
--   Powers of continuous linear functionals are total in Gaussian `L²`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianCylinderDensity.lean#L101-L217
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianCylinderDensity.lean#L101-L217

import Definitions.Def_Malliavin_PastCylinderDensity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_Malliavin_BrownianCylinderDensity
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open NormedSpace
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {E W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  (μ : Measure E) [IsGaussian μ]

theorem Malliavin.dense_gaussianPolynomialSpan :
    Dense (gaussianPolynomialSpan μ : Set (Lp ℝ 2 μ)) := by sorry
