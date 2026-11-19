-- Prove2me | Theorems.Thm_Kyprianou_Ch01_expAscendingRenewalPositiveSeries
-- name    : Kyprianou.Ch01.expAscendingRenewalPositiveSeries
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T00:55:56.220049+00:00
-- url     : https://prove2.me/theorems/cad39938-af5e-4b19-ae00-98b0c3f37d79
-- title:
--   Rate-beta exponential renewal series beyond the zero convolution power
-- statement:
--   For independent positive exponential increments of rate beta, the renewal mass contributed by all strictly positive convolution powers to [0,x] equals beta times x, with an explicitly summable sequence of nonnegative real convolution masses. Prove via gamma convolution densities and exponential Taylor series, or by a source-exact bridge to an accepted general renewal theorem. This is the non-atomic part of Exercise 1.8(iv).
-- source:
--   Kyprianou (2006), Exercise 1.8(iv), worked solution printed pp.304-305

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_QueueingFundamentals_MG1_transforms
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.expAscendingRenewalPositiveSeries
  (beta : ℝ) (hbeta : 0 < beta) :
  let mu : Measure ℝ :=
    (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun y : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * y)))
  ∀ x : ℝ, 0 ≤ x →
    Summable (fun n : ℕ => ((QueueingFundamentals.MG1.convPow mu (n + 1))
      (Set.Icc (0 : ℝ) x)).toReal) ∧
    (∑' n : ℕ, ((QueueingFundamentals.MG1.convPow mu (n + 1))
      (Set.Icc (0 : ℝ) x)).toReal) = beta * x := by sorry
