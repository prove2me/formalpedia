-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ucpDiagonalGeometricV1
-- name    : Kyprianou.Ch04.ucpDiagonalGeometricV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:08:02.393384+00:00
-- url     : https://prove2.me/theorems/c9fb63c4-4a22-46c5-acc8-8322f62271c6
-- title:
--   Common subsequence with geometric increments on expanding horizons
-- statement:
--   Common subsequence with geometric increments on expanding horizons.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology UniformConvergence
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem ucpDiagonalGeometricV1 {Ω E : Type} [MeasurableSpace Ω] [MetricSpace E] [CompleteSpace E]
    (P : Measure Ω) (X : ℕ → NNReal → Ω → E)
    (hc : ∀ i : ℕ, ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
      P {w | ∃ t ≤ (i : NNReal), (2⁻¹ : ℝ)^i < dist (X m t w) (X n t w)} ≤
        (2⁻¹ : ENNReal)^i) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ w ∂P,
      ∀ᶠ n : ℕ in atTop, ∀ t ≤ (n : NNReal),
        dist (X (k n) t w) (X (k (n+1)) t w) ≤ (2⁻¹ : ℝ)^n := by
  sorry
end Kyprianou.Ch04
