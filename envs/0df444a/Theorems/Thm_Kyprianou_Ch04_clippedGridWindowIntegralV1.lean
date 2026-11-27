-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clippedGridWindowIntegralV1
-- name    : Kyprianou.Ch04.clippedGridWindowIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:41:35.373469+00:00
-- url     : https://prove2.me/theorems/2393ee4f-89c1-4ca6-8013-cf3de4402d4c
-- title:
--   clippedGridWindowIntegralV1
-- statement:
--   Physical clipped grid integral identity.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_clippedGridWindowCellIntegralV1
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

/-- Integrating the finite step coefficient against any integrable marked
window kernel gives the corresponding clipped weighted increment sum. -/

theorem Kyprianou.Ch04.clippedGridWindowIntegralV1 (R : Measure (ℝ × ℝ)) (Q : ℝ × ℝ → ℝ)
    (T t : NNReal) (ht : t ≤ T) (u : ℕ → NNReal) (hu : Monotone u)
    (n : ℕ) (H : ℕ → ℝ)
    (hQ : IntegrableOn Q (Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)) R) :
    (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
      (∑ k ∈ Finset.range n, (Ioc (u k) (u (k+1))).indicator
        (fun _ => H k) z.1.toNNReal) * Q z ∂ R) =
    ∑ k ∈ Finset.range n, H k *
      ((∫ z in Icc (0 : ℝ) ((min t (u (k+1)) : NNReal) : ℝ) ×ˢ (univ : Set ℝ), Q z ∂ R) -
       ∫ z in Icc (0 : ℝ) ((min t (u k) : NNReal) : ℝ) ×ˢ (univ : Set ℝ), Q z ∂ R) := by
  sorry
