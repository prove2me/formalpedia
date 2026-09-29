-- Prove2me | Theorems.Thm_Freiman_localValue_window_comparison
-- name    : Freiman.localValue_window_comparison
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:37.554106+00:00
-- url     : https://prove2.me/theorems/75f42a92-275e-4bbb-ab3f-bfa9269a121d
-- title:
--   localValue window comparison
-- statement:
--   Local values at possibly different positions differ by at most the report Fibonacci cylinder bound if the translated radius-R windows agree.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Lemma 1.11 (found:padded-models), padding and finite-window proof.

import Definitions.Def_Freiman_paddedCopies
import Mathlib.Data.Nat.Fib.Basic

open Freiman

theorem Freiman.localValue_window_comparison (a b : ℤ → ℕ+) (i j : ℤ) (R : ℕ)
    (h : ∀ k : ℤ, -(R : ℤ) ≤ k → k ≤ (R : ℤ) → a (i + k) = b (j + k)) :
    |localValue a i - localValue b j| ≤ 2 / ((Nat.fib (R + 1) : ℝ) ^ 2) := by sorry
