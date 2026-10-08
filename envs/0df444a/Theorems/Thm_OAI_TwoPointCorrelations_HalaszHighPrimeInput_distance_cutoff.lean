-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_HalaszHighPrimeInput_distance_cutoff
-- name    : OAI.TwoPointCorrelations.HalaszHighPrimeInput.distance_cutoff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:39.250693+00:00
-- url     : https://prove2.me/theorems/d85e9810-1d7a-49e3-9762-a09b3978b9af
-- title:
--   Under the high-prime cosine input, the distance at the minimizing twist bounds the distance at others
-- statement:
--   Assume `HalaszHighPrimeInput`: for all sufficiently large $X$ and all $u$ with $(\log X)^{20}\le|u|\le2X$, $\sum_{p\le X}(1-|\cos(\tfrac u2\log p)|)/p\ge\tfrac1{10}\log\log X$. Let $K$ be real. Then for all sufficiently large $n$, every $X$ with $n\le X\le n^3$, every $F:\mathbb N\to\mathbb C$ with $|F(m)|\le1$ ($m\ge1$) and all reals $v,\tau$ with $|v|,|\tau|\le X$ and $|v-\tau|\ge\tfrac12$: if $\mathbb D(F,n^{i\tau};X)^2\le\mathbb D(F,n^{iv};X)^2$ (`squaredDistance F (mrtArchimedeanTwist ·) X`), then
--
--   $$2\cdot\tfrac3{100}\log\log n+K\le\mathbb D(F,m^{iv};n)^2.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.HalaszHighPrimeInput.distance_cutoff`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Filter
open Finset

theorem HalaszHighPrimeInput.distance_cutoff (hhigh : HalaszHighPrimeInput) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ X : ℕ, n ≤ X → X ≤ n^3 →
      ∀ (F : ℕ → ℂ), OneBounded F → ∀ v τ : ℝ,
      |v| ≤ X → |τ| ≤ X → 1/2 ≤ |v-τ| →
      squaredDistance F (mrtArchimedeanTwist τ) X ≤
        squaredDistance F (mrtArchimedeanTwist v) X →
      2*((3/100:ℝ)*Real.log (Real.log n))+K ≤
        squaredDistance F (mrtArchimedeanTwist v) n := by
  sorry

end OAI.TwoPointCorrelations
