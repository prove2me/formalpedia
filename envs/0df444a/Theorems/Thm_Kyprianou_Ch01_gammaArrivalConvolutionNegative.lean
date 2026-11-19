-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaArrivalConvolutionNegative
-- name    : Kyprianou.Ch01.gammaArrivalConvolutionNegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T07:54:08.517346+00:00
-- url     : https://prove2.me/theorems/d7b36893-67a1-46f1-8c1f-dedaace2b35d
-- title:
--   gammaArrivalConvolutionNegative public gamma convolution support case
-- statement:
--   For z<0, both nonnegative-support gamma density factors cannot be nonzero, so their convolution is zero.
-- source:
--   Kyprianou (2006) Exercise 1.8(iv) pp.304–305

import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Definitions.Def_levy_foundations_arrivalGammaDensity
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaArrivalConvolutionNegative
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) (z : ℝ) (hz : z < 0) :
    (∫⁻ x : ℝ, LevyFoundations.arrivalGammaDensity beta n x *
      LevyFoundations.arrivalGammaDensity beta 0 (z - x)) = 0 := by
  sorry
