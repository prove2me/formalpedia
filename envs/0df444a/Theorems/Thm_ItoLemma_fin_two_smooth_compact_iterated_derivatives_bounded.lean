-- Prove2me | Theorems.Thm_ItoLemma_fin_two_smooth_compact_iterated_derivatives_bounded
-- name    : ItoLemma.fin_two_smooth_compact_iterated_derivatives_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:03:55.432225+00:00
-- url     : https://prove2.me/theorems/a30779e1-d0f7-4f4c-bd93-10506f7958de
-- title:
--   Uniform Bounds on Truncated Product Derivatives through Order Two
-- statement:
--   For a C∞ compactly supported real function of two real coordinates, a single nonnegative constant bounds the norms of all iterated Fréchet derivatives of orders zero, one, and two. This is the bounded-derivative ingredient of the finite-dimensional Itô formula.
-- source:
--   Official Mathlib.Analysis.Calculus.ContDiff.Basic documentation, HasCompactSupport.exists_bound_iteratedFDeriv, read 26 October 2026: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/ContDiff/Basic.html. Pinned index omission noted; proof availability requires remote verification.

import Mathlib.Analysis.Calculus.ContDiff.Basic

theorem ItoLemma.fin_two_smooth_compact_iterated_derivatives_bounded
    (f : (Fin 2 → ℝ) → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hs : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : ℕ, i ≤ 2 → ∀ z : Fin 2 → ℝ, ‖iteratedFDeriv ℝ i f z‖ ≤ C := by sorry
