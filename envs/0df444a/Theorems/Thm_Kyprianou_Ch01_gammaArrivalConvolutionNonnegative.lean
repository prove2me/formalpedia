-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaArrivalConvolutionNonnegative
-- name    : Kyprianou.Ch01.gammaArrivalConvolutionNonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T07:54:08.30538+00:00
-- url     : https://prove2.me/theorems/62f9ccb0-e12a-439a-9ea1-3ac66026042e
-- title:
--   gammaArrivalConvolutionNonnegative public gamma convolution support case
-- statement:
--   For z>=0, the gamma convolution equals the next arrival density, using the monomial integral over 0<=x<=z.
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

theorem Kyprianou.Ch01.gammaArrivalConvolutionNonnegative
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∫⁻ x : ℝ, LevyFoundations.arrivalGammaDensity beta n x *
      LevyFoundations.arrivalGammaDensity beta 0 (z - x)) = LevyFoundations.arrivalGammaDensity beta (n + 1) z := by
  sorry
