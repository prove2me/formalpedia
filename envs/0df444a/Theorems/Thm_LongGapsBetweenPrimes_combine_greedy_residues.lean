-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_combine_greedy_residues
-- name    : LongGapsBetweenPrimes.combine_greedy_residues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:13.783859+00:00
-- url     : https://prove2.me/theorems/b3c6e976-b504-4337-964b-f3a920e5408e
-- title:
--   Long Gaps Between Primes: combine greedy residues
-- statement:
--   Combine a zero-residue sieve with greedy choices on a disjoint set of moduli.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4091-L4116
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4091-L4116

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.combine_greedy_residues (S ps₀ ps₁ ps : Finset ℕ)
    (h₀ : ps₀ ⊆ ps) (h₁ : ps₁ ⊆ ps) (hdisj : Disjoint ps₀ ps₁)
    (hpos : ∀ p ∈ ps, 0 < p) :
    ∃ a : ℕ → ℕ, (∀ p ∈ ps, a p < p) ∧
      ((survivors S ps a).card : ℝ) ≤
        ((survivors S ps₀ (fun _ => 0)).card : ℝ) * ∏ p ∈ ps₁, (1 - 1 / (p : ℝ)) := by sorry
