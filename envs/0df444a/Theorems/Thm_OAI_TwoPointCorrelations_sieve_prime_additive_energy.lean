-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_sieve_prime_additive_energy
-- name    : OAI.TwoPointCorrelations.sieve_prime_additive_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:45.083718+00:00
-- url     : https://prove2.me/theorems/eefca35d-e9a0-4d2a-b188-38d11286ef24
-- title:
--   The additive energy of a set of primes up to 2x is ≪ x³/log⁴x
-- statement:
--   There is $C>0$ such that for all sufficiently large $x$ and every finite set $P$ of odd primes, each at most $2x$,
--
--   $$E(P,P)\le\frac{C\,x^3}{\log^4x},$$
--
--   where $E(P,P)=\#\{(a,b,c,d)\in P^4:a+b=c+d\}$ is Mathlib's additive energy `Finset.addEnergy`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.sieve_prime_additive_energy`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open OAI.Problem337
open scoped Classical
open scoped Pointwise

theorem sieve_prime_additive_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ (p : ℝ) ≤ 2 * x) →
      (Finset.addEnergy P P : ℝ) ≤ C * x ^ 3 / Real.log x ^ 4 := by
  sorry

end OAI.TwoPointCorrelations
