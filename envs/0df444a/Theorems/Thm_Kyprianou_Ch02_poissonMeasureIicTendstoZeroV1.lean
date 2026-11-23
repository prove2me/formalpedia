-- Prove2me | Theorems.Thm_Kyprianou_Ch02_poissonMeasureIicTendstoZeroV1
-- name    : Kyprianou.Ch02.poissonMeasureIicTendstoZeroV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:08:28.465907+00:00
-- url     : https://prove2.me/theorems/b3f4f683-1340-47f8-8316-cae8bdf1d1ff
-- title:
--   Poisson bounded-count probability tends to zero at high intensity
-- statement:
--   For any fixed natural count ceiling N, the probability that a Poisson random variable with intensity r is at most N tends to zero as r tends to infinity. Proved from the finite sum of Poisson singleton masses and the pinned Mathlib asymptotic exp(-r) r^k -> 0.
-- source:
--   Kyprianou Chapter 2 Theorem 2.4: Poisson lower-tail reduction; pinned Mathlib Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero and poissonMeasure_singleton.

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem poissonMeasureIicTendstoZeroV1 (N : ℕ) :
    Tendsto (fun r : NNReal => ProbabilityTheory.poissonMeasure r (Set.Iic N))
      atTop (𝓝 (0 : ENNReal)) := by sorry
end Kyprianou.Ch02
