-- Prove2me | Theorems.Thm_Malliavin_dense_brownianPolynomialSpan
-- name    : Malliavin.dense_brownianPolynomialSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:55:27.923744+00:00
-- url     : https://prove2.me/theorems/050f072f-8f5b-429b-8c3f-6da3edd243db
-- title:
--   Malliavin: dense brownian Polynomial Span
-- statement:
--   If the Brownian coordinates generate the ambient measurable space, finite Brownian
--   polynomials are dense in ambient `L²(P)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianCylinderDensity.lean#L419-L451
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianCylinderDensity.lean#L419-L451

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
variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]

theorem Malliavin.dense_brownianPolynomialSpan
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B) :
    Dense (brownianPolynomialSpan hB : Set (RandomL2 P)) := by sorry
