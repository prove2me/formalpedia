-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_prime_triple_exception
-- name    : OAI.TwoPointCorrelations.halasz_prime_triple_exception
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:39.610995+00:00
-- url     : https://prove2.me/theorems/a476b24c-f2ae-46df-8416-2b518dd5ab5c
-- title:
--   Halász-type bound for a triple convolution with two prime polynomials, away from one exceptional frequency
-- statement:
--   There are $C>0$ and $B\ge2$ such that the following holds. Let $f$ be completely multiplicative on positive integers with $f(1)=1$ and $|f(n)|\le1$ ($n\ge1$), $N\in\mathbb N$, and $f_N$ = `halaszSmoothFunction f N` ($f$ on numbers all of whose prime factors are at most $N$, $0$ elsewhere). Let $x>0$ non-integral, $1\le m\le x$ an integer, $T\ge B$, $A,W,R\ge0$, $\tau$ real, $P$ a finite set of primes $p\ge T^2$, $Q$ a finite set of primes, $a,b:\mathbb N\to\mathbb C$ with $|a|\le R$ on $P$ and $|b|\le1$ on $Q$. Suppose $|L(f_N,1+it)|\le A$ for $t\in(-T,T]\setminus(\tau-\frac12,\tau+\frac12]$ and $|L(f_N,1+it)|\le W$ for all real $t$. Then, with $\alpha=\mathbf 1_P\log\cdot\,a$, $\beta=\mathbf 1_Q\log\cdot\,b$ and Dirichlet convolution $*$,
--
--   $$\Big|\sum_{1\le n\le x}(\alpha*\beta*f_N)(n)\Big|\le Cx\Big(A+\frac W{1+|\tau|}\Big)\Big(\sum_P|a(p)|^2\tfrac{\log p}p\Big)^{1/2}\Big(\sum_Q|b(q)|^2\tfrac{\log q}q\Big)^{1/2}+\frac{40x(R\sum_P\frac{\log p}p)(\sum_Q\frac{\log q}q)W}{(m/x)T}+R\log^2(x+m)\,m.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_prime_triple_exception`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Complex
open MeasureTheory
open _root_.Erdos970 (VerticalIntegral VerticalIntegral')
open scoped Classical
open scoped LSeries.notation

theorem halasz_prime_triple_exception : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n) → OneBounded f →
    ∀ (N : ℕ) (x T A W τ R : ℝ) (m : ℕ), 0 < x → 0 < m → (m : ℝ) ≤ x →
      (∀ n : ℕ, x ≠ (n : ℝ)) → B ≤ T → 0 ≤ A → 0 ≤ W → 0 ≤ R →
    ∀ (P Q : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ)) →
      (∀ q ∈ Q, q.Prime) → ∀ a b : ℕ → ℂ,
      (∀ p ∈ P, ‖a p‖ ≤ R) → (∀ q ∈ Q, ‖b q‖ ≤ 1) →
      (∀ t ∈ Set.Ioc (-T) T, t ∉ Set.Ioc (τ-1/2) (τ+1/2) →
        ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ A) →
      (∀ t : ℝ, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ W) →
    ‖∑ n ∈ Icc 1 ⌊x⌋₊,
      (halaszFiniteCoefficient P (fun p => (Real.log (p : ℝ) : ℂ) * a p) ⍟
        (halaszFiniteCoefficient Q (fun q => (Real.log (q : ℝ) : ℂ) * b q) ⍟
          halaszSmoothFunction f N)) n‖ ≤
      (C * x * (A+W/(1+|τ|))) *
        (Real.sqrt (∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)) *
          Real.sqrt (∑ q ∈ Q, ‖b q‖ ^ 2 * (Real.log (q : ℝ) / q))) +
      40 * x * (R * ∑ p ∈ P, Real.log (p : ℝ) / p) *
        (∑ q ∈ Q, Real.log (q : ℝ) / q) * W / ((m / x) * T) +
      R * Real.log (x + m) ^ 2 * m := by
  sorry

end OAI.TwoPointCorrelations
