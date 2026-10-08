-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_mixed_double_estimate
-- name    : OAI.TwoPointCorrelations.halasz_mixed_double_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:34.879995+00:00
-- url     : https://prove2.me/theorems/2d8552d0-5234-4d0d-8ef4-0728b59db38e
-- title:
--   Halász bound for the mixed prime double convolution of two bounded functions
-- statement:
--   There are $C>0$ and $T_0\ge2$ such that for all $G,B:\mathbb N\to\mathbb C$ bounded by $1$ on positive integers, naturals $N\ge2$, $1\le m\le N$, and reals $R\ge1$, $T$ with $T^2\le R$ and $T\ge T_0$, $V\ge\log N$, $W\ge0$, $M\ge0$: if $|L(B_N,1+it)|\le Ve^{-M}$ for $t\in[-T,T]$ and $|L(B_N,1+it)|\le W$ for all real $t$, where $B_N$ = `halaszSmoothFunction B N` is $B$ restricted to the numbers all of whose prime factors are at most $N$, then
--
--   $$\big|\texttt{halaszMixedDouble}\ G\ B\ N\ R\big|\le CNV(M+1)e^{-M}+\frac{CNW\log N}{(m/(N+\frac12))\,T}+Cm\log^2(3N),$$
--
--   where `halaszMixedDouble G B N R` $=\sum_p\log p\,G(p)\,\texttt{halaszMixedPrimeConvolution}(G,B,\lfloor N/p\rfloor,R,\lfloor N/p\rfloor)/\log(N/p)$ over the primes of `mrtPrimeBand R (N/2)`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_mixed_double_estimate`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Complex
open scoped Classical

theorem halasz_mixed_double_estimate : ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
    ∀ (G B : ℕ → ℂ), OneBounded G → OneBounded B →
    ∀ (N m : ℕ) (R T V W M : ℝ), 2 ≤ N → 0 < m → m ≤ N →
      1 ≤ R → T ^ 2 ≤ R → T₀ ≤ T → Real.log N ≤ V → 0 ≤ W → 0 ≤ M →
      (∀ t ∈ Set.Icc (-T) T,
        ‖LSeries (halaszSmoothFunction B N) (1 + (t : ℂ) * I)‖ ≤ V * Real.exp (-M)) →
      (∀ t : ℝ, ‖LSeries (halaszSmoothFunction B N) (1 + (t : ℂ) * I)‖ ≤ W) →
      ‖halaszMixedDouble G B N R‖ ≤
        C * N * V * (M + 1) * Real.exp (-M) +
        C * N * W * Real.log N / (((m : ℝ) / ((N : ℝ) + 1 / 2)) * T) +
        C * m * Real.log (3 * N) ^ 2 := by
  sorry

end OAI.TwoPointCorrelations
