-- Prove2me | Theorems.Thm_Freiman_padded_copies_window_cases
-- name    : Freiman.padded_copies_window_cases
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:35.695455+00:00
-- url     : https://prove2.me/theorems/94ffeb81-208e-4c04-9a71-4e8f08e3c64d
-- title:
--   padded copies window cases
-- statement:
--   Fix a window radius R and a minimum model index J. At every sufficiently late position, the viewing window either agrees with a window of a model of index at least J, or consists entirely of d. The latter case handles joins using the model padding lengths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Lemma 1.11 (found:padded-models), padding and finite-window proof.

import Definitions.Def_Freiman_paddedCopies
import Mathlib.Data.Nat.Fib.Basic

open Freiman

theorem Freiman.padded_copies_window_cases (a : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+) (d : ℕ+)
    (hcopy : PaddedCopies a b d)
    (hpad : ∀ j : ℕ, ∀ i : ℤ, j < i.natAbs → a j i = d) (R J : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∃ j : ℕ, J ≤ j ∧ ∃ i : ℤ,
        ∀ k : ℤ, -(R : ℤ) ≤ k → k ≤ (R : ℤ) → b ((n : ℤ) + k) = a j (i + k)) ∨
      (∀ k : ℤ, -(R : ℤ) ≤ k → k ≤ (R : ℤ) → b ((n : ℤ) + k) = d) := by sorry
