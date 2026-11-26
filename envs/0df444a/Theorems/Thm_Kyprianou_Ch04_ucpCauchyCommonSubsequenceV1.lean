-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ucpCauchyCommonSubsequenceV1
-- name    : Kyprianou.Ch04.ucpCauchyCommonSubsequenceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:04:38.961632+00:00
-- url     : https://prove2.me/theorems/fdb309ec-c224-4669-9a58-49437c82bdf6
-- title:
--   Summable-probability common compact Cauchy subsequence
-- statement:
--   Summable-probability common compact Cauchy subsequence.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology UniformConvergence
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem ucpCauchyCommonSubsequenceV1 {Ω E : Type} [MeasurableSpace Ω] [MetricSpace E] [CompleteSpace E]
    (P : Measure Ω) (X : ℕ → NNReal → Ω → E)
    (hc : ∀ i : ℕ, ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
      P {w | ∃ t ≤ (i : NNReal), (2⁻¹ : ℝ)^i < dist (X m t w) (X n t w)} ≤
        (2⁻¹ : ENNReal)^i) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ w ∂P, ∀ T : NNReal,
      UniformCauchySeqOn (fun n t => X (k n) t w) atTop (Icc 0 T) := by
  sorry
end Kyprianou.Ch04
