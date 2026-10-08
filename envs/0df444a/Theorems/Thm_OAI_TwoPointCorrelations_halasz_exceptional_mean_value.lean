-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_exceptional_mean_value
-- name    : OAI.TwoPointCorrelations.halasz_exceptional_mean_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:14.179298+00:00
-- url     : https://prove2.me/theorems/4ef5c978-ffe6-4ea0-b2e1-ff03d8bd985f
-- title:
--   Halász's mean-value theorem with one exceptional frequency
-- statement:
--   There are $C>0$ and $X_0$ such that for every natural $N\ge X_0$, every completely multiplicative $f$ (on positive integers) with $f(1)=1$ and $|f(n)|\le1$ for $n\ge1$, and all reals $M\ge0$, $\tau$: if $\mathbb D(f,n^{it};N)^2\ge M$ (`squaredDistance f (mrtArchimedeanTwist t) N` $=\sum_{p\le N}(1-\operatorname{Re}f(p)p^{-it})/p$) for every $t\in(-(\log N)^8,(\log N)^8]$ outside $(\tau-\tfrac12,\tau+\tfrac12]$, then
--
--   $$\Big|\sum_{n=1}^Nf(n)\Big|\le CN\Big((\mu+1)e^{-\mu}+\frac{\log\log N}{\log N}\Big),\qquad\mu=\min(M,\log(1+|\tau|)).$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_exceptional_mean_value`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter

theorem halasz_exceptional_mean_value : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ (N : ℕ), X₀ ≤ N →
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ a b, 0 < a → 0 < b → f (a * b) = f a * f b) → OneBounded f →
    ∀ (M τ : ℝ), 0 ≤ M →
      (∀ t ∈ Set.Ioc (-(Real.log (N : ℝ) ^ 8)) (Real.log (N : ℝ) ^ 8),
        t ∉ Set.Ioc (τ-1/2) (τ+1/2) → M ≤ squaredDistance f (mrtArchimedeanTwist t) N) →
      ‖∑ n ∈ Icc 1 N, f n‖ ≤ C * N *
        ((min M (Real.log (1+|τ|)) + 1) * Real.exp (-min M (Real.log (1+|τ|))) +
          Real.log (Real.log N) / Real.log N) := by
  sorry

end OAI.TwoPointCorrelations
