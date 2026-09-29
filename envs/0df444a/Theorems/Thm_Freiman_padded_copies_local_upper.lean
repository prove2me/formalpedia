-- Prove2me | Theorems.Thm_Freiman_padded_copies_local_upper
-- name    : Freiman.padded_copies_local_upper
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:43.43319+00:00
-- url     : https://prove2.me/theorems/94354dba-5668-4256-823c-dddd4464865d
-- title:
--   padded copies local upper
-- statement:
--   Once all sufficiently late model errors are at most δ, late local values of the copied word are at most t+δ plus the radius-R cylinder error. This combines the two window cases with their correct local upper bounds.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Lemma 1.11 (found:padded-models), padding and finite-window proof.

import Definitions.Def_Freiman_paddedCopies
import Mathlib.Data.Nat.Fib.Basic

open Freiman

theorem Freiman.padded_copies_local_upper (a : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+) (d : ℕ+) (t : ℝ) (ε : ℕ → ℝ)
    (hcopy : PaddedCopies a b d)
    (hpad : ∀ j : ℕ, ∀ i : ℤ, j < i.natAbs → a j i = d)
    (hbound : ∀ j : ℕ, ∀ i : ℤ, localValue (a j) i ≤ t + ε j)
    (hbackground : Real.sqrt ((((d : ℕ) : ℝ) ^ 2) + 4) ≤ t)
    (R J : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hJ : ∀ j : ℕ, J ≤ j → ε j ≤ δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → localValue b (n : ℤ) ≤ t + δ + 2 / ((Nat.fib (R + 1) : ℝ) ^ 2) := by sorry
