-- Prove2me | Theorems.Thm_Malliavin_setIntegral_predictableProjection
-- name    : Malliavin.setIntegral_predictableProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:26:25.760903+00:00
-- url     : https://prove2.me/theorems/fdc22e84-32c0-5047-bd53-c5c22ddbf155
-- title:
--   Malliavin: set Integral predictable Projection
-- statement:
--   The predictable projection preserves integrals over every predictable set of finite
--   measure.  This extends `integral_predictableProjection_Ioc` from predictable rectangles to the
--   whole predictable σ-algebra.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L71-L76
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L71-L76

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.setIntegral_predictableProjection
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) {s : Set (ℝ≥0 × W)}
    (hs : MeasurableSet[𝓕.predictable] s) (hμs : (nonnegativeLebesgueMeasure.prod P) s ≠ ∞) :
    ∫ x in s, (predictableProjection 𝓕 U : (ℝ≥0 × W) → ℝ) x ∂(nonnegativeLebesgueMeasure.prod P)
      = ∫ x in s, U x ∂(nonnegativeLebesgueMeasure.prod P) := by sorry
