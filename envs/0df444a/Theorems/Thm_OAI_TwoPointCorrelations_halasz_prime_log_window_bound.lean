-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_prime_log_window_bound
-- name    : OAI.TwoPointCorrelations.halasz_prime_log_window_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:23.722486+00:00
-- url     : https://prove2.me/theorems/b6d2d066-d0ea-4c59-af89-a54992f4750b
-- title:
--   Primes in a short logarithmic window contribute at most C/T to Σ log p / p
-- statement:
--   There are $C>0$ and $B\ge2$ such that for all reals $T\ge B$, $u\ge1$ with $T^2\le e^u$, and every finite set $P$ of primes with $u\le\log p\le u+1/T$ for $p\in P$,
--
--   $$\sum_{p\in P}\frac{\log p}{p}\le\frac CT.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_prime_log_window_bound`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open scoped BigOperators

theorem halasz_prime_log_window_bound : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (T u : ℝ) (P : Finset ℕ), B ≤ T → 1 ≤ u → T ^ 2 ≤ Real.exp u →
      (∀ p ∈ P, p.Prime ∧ u ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ u + 1 / T) →
      (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) ≤ C / T := by
  sorry

end OAI.TwoPointCorrelations
