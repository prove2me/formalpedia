-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_double_convolution_exception
-- name    : OAI.TwoPointCorrelations.halasz_double_convolution_exception
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:58.753088+00:00
-- url     : https://prove2.me/theorems/552853ee-69a7-4e43-886b-b177d3ddb5af
-- title:
--   Halász bound for the prime-weighted double convolution away from one exceptional frequency
-- statement:
--   There are $C>0$ and $B\ge2$ such that: for every completely multiplicative $f$ (on positive integers) with $f(1)=1$ and $|f(n)|\le1$ for $n\ge1$, all naturals $N\ge2$ and $1\le m\le N$, and reals $L,T,V,W,M_0,\tau$ with $L\ge1$, $T^2\le L$, $T\ge B$, $V\ge\log N$, $W,M_0\ge0$, if $|L(f_N,1+it)|\le Ve^{-M_0}$ for all $t\in(-T,T]$ outside $(\tau-\tfrac12,\tau+\tfrac12]$ and $|L(f_N,1+it)|\le W$ for all real $t$ (with $f_N$ = `halaszSmoothFunction f N`, the restriction of $f$ to $(N+1)$-smooth numbers), then, writing $\mu=\min(M_0,\log(1+|\tau|))$,
--
--   $$\big|\texttt{halaszDoubleConvolution}\ f\ N\ L\big|\le CN(V+W)(\mu+1)e^{-\mu}+\frac{CNW\log N}{(m/(N+\frac12))\,T}+Cm\log^2(3N).$$
--
--   Here `halaszDoubleConvolution f N L` $=\sum_{p}\log p\,f(p)\,\frac{(\text{prime convolution of }f\text{ at }\lfloor N/p\rfloor)}{\log(N/p)}$, the sum over the primes of `mrtPrimeBand L (N/2)`, with the bundle's `halaszPrimeConvolution`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_double_convolution_exception`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Complex
open scoped Classical

theorem halasz_double_convolution_exception : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ a b, 0 < a → 0 < b → f (a * b) = f a * f b) → OneBounded f →
    ∀ (N m : ℕ) (L T V W M₀ τ : ℝ), 2 ≤ N → 0 < m → m ≤ N →
      1 ≤ L → T ^ 2 ≤ L → B ≤ T → Real.log N ≤ V → 0 ≤ W → 0 ≤ M₀ →
      (∀ t ∈ Set.Ioc (-T) T, t ∉ Set.Ioc (τ-1/2) (τ+1/2) →
        ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ V * Real.exp (-M₀)) →
      (∀ t : ℝ, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ W) →
      ‖halaszDoubleConvolution f N L‖ ≤
        C * N * (V+W) * (min M₀ (Real.log (1+|τ|)) + 1) *
          Real.exp (-min M₀ (Real.log (1+|τ|))) +
        C * N * W * Real.log N / (((m : ℝ) / ((N : ℝ) + 1 / 2)) * T) +
        C * m * Real.log (3 * N) ^ 2 := by
  sorry

end OAI.TwoPointCorrelations
