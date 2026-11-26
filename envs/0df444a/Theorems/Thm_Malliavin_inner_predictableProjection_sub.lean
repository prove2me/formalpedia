-- Prove2me | Theorems.Thm_Malliavin_inner_predictableProjection_sub
-- name    : Malliavin.inner_predictableProjection_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:19:39.288801+00:00
-- url     : https://prove2.me/theorems/63227620-3c52-57f3-8f12-b2eac7c1fc67
-- title:
--   Malliavin: inner predictable Projection sub
-- statement:
--   The predictable projection is orthogonal: the correction `Π U - U` is orthogonal to every
--   predictable process.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L424-L430
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L424-L430

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
  [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.inner_predictableProjection_sub (U : TimeProcessL2 P) (V : PredictableProcessL2 𝓕 P) :
    ⟪(predictableProjection 𝓕 U : TimeProcessL2 P) - U, (V : TimeProcessL2 P)⟫_ℝ = 0 := by sorry
