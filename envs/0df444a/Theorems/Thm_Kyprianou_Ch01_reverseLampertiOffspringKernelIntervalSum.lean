-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiOffspringKernelIntervalSum
-- name    : Kyprianou.Ch01.reverseLampertiOffspringKernelIntervalSum
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T18:39:22.748847+00:00
-- url     : https://prove2.me/theorems/47d3abd4-f9b9-4db5-b6e3-5a3398e29584
-- title:
--   Offspring series under the exponential integral
-- statement:
--   The exponential weight $\lambda e^{-\lambda a}$ does not depend on the offspring index, so the sum over $j$ of the integrals equals the integral of the sum
--   $$\int_0^{yt}\lambda e^{-\lambda a}\sum_j p_j K_{y-1+j}(t-a/y,k)\,da.$$
-- source:
--   Kyprianou (2006), Section 1.3.4; marked first-event mixture of the nonexplosive inverse Lamperti law.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory Kyprianou.Ch01
open scoped NNReal BigOperators Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiOffspringKernelIntervalSum
    (rate : ℝ≥0) (offspring : PMF ℕ) (K : PopulationLaws)
    (y : ℕ) (t : ℝ≥0) (k : ℕ) :
    ∑' j : ℕ, ∫ a in (0 : ℝ)..(y : ℝ) * (t : ℝ),
        (rate : ℝ) * Real.exp (-((rate : ℝ) * a)) * (offspring j).toReal *
          (K ((y - 1) + j)
            (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal =
      ∫ a in (0 : ℝ)..(y : ℝ) * (t : ℝ),
        (rate : ℝ) * Real.exp (-((rate : ℝ) * a)) *
          ∑' j : ℕ, (offspring j).toReal *
            (K ((y - 1) + j)
              (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal := by
  sorry
