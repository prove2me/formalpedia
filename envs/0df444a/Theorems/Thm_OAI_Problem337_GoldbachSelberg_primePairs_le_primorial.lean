-- Prove2me | Theorems.Thm_OAI_Problem337_GoldbachSelberg_primePairs_le_primorial
-- name    : OAI.Problem337.GoldbachSelberg.primePairs_le_primorial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:38.185763+00:00
-- url     : https://prove2.me/theorems/3454af53-b245-4b38-bfcd-83eb24b4a1b1
-- title:
--   A Selberg sieve upper bound for prime pairs summing to N
-- statement:
--   Let $N$ be even and $z\ge1$. Then
--
--   $$\#\,\mathrm{primePairs}(N)\le\frac{N-1}{G(N,z)}+z^2(1+\log z)^4+2\,\pi(z),$$
--
--   where `primePairs N` is the set of $x\in\{1,\dots,N-1\}$ with $x$ and $N-x$ both prime, $G(N,z)$ is `denominator N (primorial z) z` $=\sum_{d\mid \prod_{p\le z}p,\ d\le z} g_N(d)\prod_{p\mid d}(1-g_N(p))^{-1}$ with $g_N$ the bundle's sieve density `goldbachSieveDensity N`, $N-1$ is natural-number subtraction, and $\pi(z)$ is the number of primes at most $z$ (`Nat.primesLE z`).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.Problem337.GoldbachSelberg.primePairs_le_primorial`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.Problem337.GoldbachSelberg

open scoped BigOperators
open Finset

theorem primePairs_le_primorial (N : ℕ) (hN : 2 ∣ N) {z : ℕ} (hz : 1 ≤ z) :
    ((PrimePairSieve.primePairs N).card : ℝ) ≤
      ((N - 1 : ℕ) : ℝ) / denominator N (primorial z) z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * (Nat.primesLE z).card := by
  sorry

end OAI.Problem337.GoldbachSelberg
