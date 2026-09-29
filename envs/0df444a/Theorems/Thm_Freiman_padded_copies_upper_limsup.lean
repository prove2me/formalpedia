-- Prove2me | Theorems.Thm_Freiman_padded_copies_upper_limsup
-- name    : Freiman.padded_copies_upper_limsup
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:49.37877+00:00
-- url     : https://prove2.me/theorems/d11b4786-082f-4266-9b0e-502fa02fa14a
-- title:
--   padded copies upper limsup
-- statement:
--   The model errors tend to zero and the Fibonacci window bound tends to zero. Applying the finite-window upper estimate first at a chosen radius and then at sufficiently late positions gives precisely the upper epsilon condition at t.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Lemma 1.11 (found:padded-models), padding and finite-window proof.

import Definitions.Def_Freiman_paddedCopies
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Topology.Instances.Real.Lemmas

open Freiman

theorem Freiman.padded_copies_upper_limsup (a : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+) (d : ℕ+) (t : ℝ) (ε : ℕ → ℝ)
    (hcopy : PaddedCopies a b d)
    (hpad : ∀ j : ℕ, ∀ i : ℤ, j < i.natAbs → a j i = d)
    (hbound : ∀ j : ℕ, ∀ i : ℤ, localValue (a j) i ≤ t + ε j)
    (heps : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hbackground : Real.sqrt ((((d : ℕ) : ℝ) ^ 2) + 4) ≤ t) :
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → localValue b (n : ℤ) ≤ t + η := by sorry
