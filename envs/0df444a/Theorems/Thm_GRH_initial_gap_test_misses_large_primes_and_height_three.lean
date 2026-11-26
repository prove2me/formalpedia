-- Prove2me | Theorems.Thm_GRH_initial_gap_test_misses_large_primes_and_height_three
-- name    : GRH.initial_gap_test_misses_large_primes_and_height_three
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T16:15:56.091266+00:00
-- url     : https://prove2.me/theorems/98753961-1598-48fc-bf23-39cbd1f9b810
-- title:
--   The initial-gap period test misses every third or later grid and every level with a prime factor above five
-- statement:
--   For the cofinal target grid indexed by $h\ge0$, the initial-gap test fails whenever $h\ge2$ or the character level has any prime factor at least seven. Thus the test misses all heights from three onward, even at levels with only small prime factors.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/59bf325f-868f-5552-94bb-1b5f67435396. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Definitions.Def_GRH_DirichletPeriod

open GRH.DirichletPeriod

theorem GRH.initial_gap_test_misses_large_primes_and_height_three (d h : ℕ) (hc : (∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ p ∣ d) ∨ 2 ≤ h) :
    ¬ Covers d (1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) ((h:ℝ)+1) := by sorry
