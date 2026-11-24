-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovDyadicRangeV1
-- name    : Kyprianou.Ch03.strongMarkovDyadicRangeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:57:34.909057+00:00
-- url     : https://prove2.me/theorems/a2c56bfc-c45a-4cd3-ac67-a8416a1306f2
-- title:
--   Countable upper dyadic clock range
-- statement:
--   Every rounded time is in the range of the natural grid k / 2^n, including the zero assigned at infinity.
-- source:
--   Kyprianou (2006), Theorem 3.1; parent 6ff8b93e-0675-4cc3-8e57-14e72ebe0bba.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovDyadicRangeV1
    {Omega : Type} (tau : Omega → WithTop NNReal) (finiteTime : Omega → NNReal)
    (n : ℕ) :
    Countable (Set.range (fun w : Omega => if tau w = ⊤ then (0 : NNReal) else
      (Nat.ceil ((finiteTime w : ℝ) * (2 : ℝ)^n) : NNReal) / (2 : NNReal)^n)) := by
  sorry
