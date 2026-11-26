-- Prove2me | Theorems.Thm_Kyprianou_Ch04_gluedLocalMartingaleStoppedEqV1
-- name    : Kyprianou.Ch04.gluedLocalMartingaleStoppedEqV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:15:09.380783+00:00
-- url     : https://prove2.me/theorems/50cd6b23-3ae8-466d-8f8e-d4cbc665100c
-- title:
--   Consistent stopped family gluing identity
-- statement:
--   The least index with a stopping time beyond the current clipped time is no greater than the given index. Consistency then identifies the glued process with the given stopped process.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iv).

import Mathlib
open MeasureTheory Filter
open scoped NNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem gluedLocalMartingaleStoppedEqV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (M : ℕ → NNReal → Ω → ℝ) (τ : ℕ → Ω → NNReal)
    (hτ : ∀ᵐ w ∂P, Monotone (fun n => τ n w))
    (hM : ∀ᵐ w ∂P, ∀ n m : ℕ, n ≤ m → ∀ t,
      M m (min t (τ n w)) w = M n (min t (τ n w)) w) :
    ∀ᵐ w ∂P, ∀ n t,
      (if h : ∃ k : ℕ, min t (τ n w) ≤ τ k w then
        M (Nat.find h) (min t (τ n w)) w else 0) =
      M n (min t (τ n w)) w := by
  sorry
end Kyprianou.Ch04
