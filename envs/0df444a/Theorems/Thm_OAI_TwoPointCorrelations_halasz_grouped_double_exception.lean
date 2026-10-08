-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_grouped_double_exception
-- name    : OAI.TwoPointCorrelations.halasz_grouped_double_exception
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:50.625385+00:00
-- url     : https://prove2.me/theorems/e65a2670-f16d-4c05-a58c-363f334fd97d
-- title:
--   Halász bound for the prime-grouped double convolution over one logarithmic band
-- statement:
--   There are $C>0$ and $B\ge2$ such that: for every completely multiplicative $f$ (on positive integers) with $f(1)=1$ and $|f(n)|\le1$ ($n\ge1$), naturals $N\ge2$, $1\le m\le N$, reals $v\ge\log2$, $T\ge B$, $A,W\ge0$, $\tau$, and every finite set $P$ of primes with $p\ge T^2$ and $v\le\log(N/p)<2v$, if $|L(f_N,1+it)|\le A$ for $t\in(-T,T]$ outside $(\tau-\tfrac12,\tau+\tfrac12]$ and $|L(f_N,1+it)|\le W$ for all $t$ (with $f_N$ = `halaszSmoothFunction f N`), then
--
--   $$\big|\texttt{halaszGroupedDouble}\ f\ N\ P\big|\le CN\Big(A+\frac{W}{1+|\tau|}\Big)+\frac{CNvW}{(m/(N+\frac12))\,T}+\frac mv\log^2(3N),$$
--
--   where `halaszGroupedDouble f N P` $=\sum_{p\in P}\log p\,f(p)\,\texttt{halaszPrimeConvolution}(f,\lfloor N/p\rfloor)/\log(N/p)$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_grouped_double_exception`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Complex
open scoped Classical
open scoped LSeries.notation

theorem halasz_grouped_double_exception : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n) → OneBounded f →
    ∀ (N m : ℕ) (v T A W τ : ℝ), 2 ≤ N → 0 < m → m ≤ N → Real.log 2 ≤ v →
      B ≤ T → 0 ≤ A → 0 ≤ W →
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ) ∧
      v ≤ Real.log ((N : ℝ) / p) ∧ Real.log ((N : ℝ) / p) < 2 * v) →
      (∀ t ∈ Set.Ioc (-T) T, t ∉ Set.Ioc (τ-1/2) (τ+1/2) →
        ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ A) →
      (∀ t : ℝ, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ W) →
      ‖halaszGroupedDouble f N P‖ ≤ C * N * (A+W/(1+|τ|)) +
        C * N * v * W / (((m : ℝ) / ((N : ℝ) + 1 / 2)) * T) +
        (m : ℝ) / v * Real.log (3 * N) ^ 2 := by
  sorry

end OAI.TwoPointCorrelations
