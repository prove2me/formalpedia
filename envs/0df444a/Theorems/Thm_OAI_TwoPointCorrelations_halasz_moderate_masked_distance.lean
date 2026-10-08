-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_moderate_masked_distance
-- name    : OAI.TwoPointCorrelations.halasz_moderate_masked_distance
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:31.61976+00:00
-- url     : https://prove2.me/theorems/c0ba5d0c-6e2a-4267-bbcb-cec5fd7a6552
-- title:
--   Masking finitely many primes keeps the twisted distance at least (log log N)/16 − 1/2 at moderate separations
-- statement:
--   For all sufficiently large $y$: for every $F:\mathbb N\to\mathbb C$ bounded by $1$ on positive integers, every finite set $Q$, every natural $N$ with $\log N=y^4$, and reals $t,t_1$ with $1\le|t-t_1|y^2$ and $|t-t_1|\le y^{80}$, if $\mathbb D(F,n^{it_1};N)^2\le\mathbb D(F,n^{it};N)^2$, then
--
--   $$\frac{\log\log N}{16}-\frac12\le\mathbb D(F_Q,n^{it};N)^2,$$
--
--   where $F_Q$ = `mrtMissingCoefficient F Q` is $F$ on the integers with no prime factor in $Q$ and $0$ elsewhere, and $\mathbb D(\cdot,n^{it};N)^2$ is `squaredDistance · (mrtArchimedeanTwist t) N` $=\sum_{p\le N}(1-\operatorname{Re}(\cdot)(p)p^{-it})/p$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_moderate_masked_distance`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Topology

theorem halasz_moderate_masked_distance :
    ∀ᶠ y : ℝ in atTop, ∀ (F : ℕ → ℂ), OneBounded F →
      ∀ (Q : Finset ℕ) (N : ℕ) (t t₁ : ℝ), Real.log N = y ^ 4 →
      1 ≤ |t - t₁| * y ^ 2 → |t - t₁| ≤ y ^ 80 →
      squaredDistance F (mrtArchimedeanTwist t₁) N ≤
        squaredDistance F (mrtArchimedeanTwist t) N →
      Real.log (Real.log N) / 16 - 1 / 2 ≤
        squaredDistance (mrtMissingCoefficient F Q) (mrtArchimedeanTwist t) N := by
  sorry

end OAI.TwoPointCorrelations
