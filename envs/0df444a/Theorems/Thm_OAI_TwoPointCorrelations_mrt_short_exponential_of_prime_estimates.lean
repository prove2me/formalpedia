-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_short_exponential_of_prime_estimates
-- name    : OAI.TwoPointCorrelations.mrt_short_exponential_of_prime_estimates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:30.328037+00:00
-- url     : https://prove2.me/theorems/650ce372-1694-4fa3-8010-32129dedccea
-- title:
--   The Matomäki–Radziwiłł short exponential-sum input follows from the two Halász prime inputs
-- statement:
--   If `HalaszPrimeSparseInput` and `HalaszHighPrimeInput` hold, then `MRTShortExponentialInput` holds.
--
--   Here `HalaszPrimeSparseInput` is the bundle's large-values estimate for short prime polynomials at well-spaced points, `HalaszHighPrimeInput` is the lower bound $\sum_{p\le X}(1-|\cos(\frac u2\log p)|)/p\ge\frac1{10}\log\log X$ for large $X$ and $(\log X)^{20}\le|u|\le2X$, and `MRTShortExponentialInput` is: there is $C>0$ such that for all naturals $10\le H\le X$, every multiplicative $b$ bounded by $1$ on positive integers, every $M$ with `MRTDistanceLowerBound b X H M` and every real $\alpha$, $\int_0^X|\sum_{y<n\le y+H}b(n)e(n\alpha)|\,dy\le CHX(e^{-M/20}+\frac{\log\log H}{\log H}+(\log X)^{-1/700})$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_short_exponential_of_prime_estimates`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Filter

theorem mrt_short_exponential_of_prime_estimates
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    MRTShortExponentialInput := by
  sorry

end OAI.TwoPointCorrelations
