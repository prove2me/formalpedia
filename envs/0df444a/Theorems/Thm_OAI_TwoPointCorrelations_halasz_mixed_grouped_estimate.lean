-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_mixed_grouped_estimate
-- name    : OAI.TwoPointCorrelations.halasz_mixed_grouped_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:16.648327+00:00
-- url     : https://prove2.me/theorems/b5a7921f-e060-4a16-b4c1-60c108efc135
-- title:
--   Halász bound for the mixed prime convolution grouped over one logarithmic band
-- statement:
--   There are $C>0$ and $T_0\ge2$ such that for all $G,B:\mathbb N\to\mathbb C$ bounded by $1$ on positive integers, reals $R\ge0$, naturals $N\ge2$, $1\le m\le N$, reals $v\ge\log2$, $T\ge T_0$, $A,W\ge0$, and every finite set $P$ of primes with $p\ge T^2$ and $v\le\log(N/p)<2v$: if $|L(B_N,1+it)|\le A$ for $t\in[-T,T]$ and $|L(B_N,1+it)|\le W$ for all $t$ (with $B_N$ = `halaszSmoothFunction B N`), then
--
--   $$\big|\texttt{halaszMixedGrouped}\ G\ B\ N\ R\ P\big|\le CNA+\frac{CNvW}{(m/(N+\frac12))\,T}+\frac mv\log^2(3N),$$
--
--   where `halaszMixedGrouped G B N R P` $=\sum_{p\in P}\log p\,G(p)\,\texttt{halaszMixedPrimeConvolution}(G,B,\lfloor N/p\rfloor,R,\lfloor N/p\rfloor)/\log(N/p)$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_mixed_grouped_estimate`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Complex
open scoped Classical
open scoped LSeries.notation

theorem halasz_mixed_grouped_estimate : ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
    ∀ (G B : ℕ → ℂ), OneBounded G → OneBounded B →
    ∀ (N m : ℕ) (R v T A W : ℝ), 0 ≤ R → 2 ≤ N → 0 < m → m ≤ N → Real.log 2 ≤ v →
      T₀ ≤ T → 0 ≤ A → 0 ≤ W →
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ) ∧
      v ≤ Real.log ((N : ℝ) / p) ∧ Real.log ((N : ℝ) / p) < 2 * v) →
      (∀ t ∈ Set.Icc (-T) T, ‖LSeries (halaszSmoothFunction B N) (1 + (t : ℂ) * I)‖ ≤ A) →
      (∀ t : ℝ, ‖LSeries (halaszSmoothFunction B N) (1 + (t : ℂ) * I)‖ ≤ W) →
      ‖halaszMixedGrouped G B N R P‖ ≤ C * N * A +
        C * N * v * W / (((m : ℝ) / ((N : ℝ) + 1 / 2)) * T) +
        (m : ℝ) / v * Real.log (3 * N) ^ 2 := by
  sorry

end OAI.TwoPointCorrelations
