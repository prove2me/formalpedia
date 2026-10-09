-- Prove2me | Theorems.Thm_Helfgott_centered_prime_convolution_sqrt_certificate
-- name    : Helfgott.centered_prime_convolution_sqrt_certificate
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:35:48.083989+00:00
-- url     : https://prove2.me/theorems/3997068e-e13a-4a33-a2d2-646bfaa0cd8f
-- title:
--   Exact square-root decomposition and bound for the centered prime convolution
-- statement:
--   Let $N\ge1$ be an integer and $C\in\mathbb R$. Write $\Lambda$ for the von Mangoldt function, $\psi(t)=\sum_{n\le t}\Lambda(n)$, $y=\sqrt N$, $R(t)=\psi(t)-t$, and
--   $$r_C(y)=\sum_{1\le d\le y}\frac{\Lambda(d)}d-\log y+\frac C2,\qquad
--   A_C(N)=\sum_{n=1}^N\big((\Lambda*\Lambda)(n)-\Lambda(n)\log n+C\big).$$
--   Here $*$ denotes Dirichlet convolution. Then
--   $$A_C(N)=-1+2\sum_{1\le d\le y}\Lambda(d)R(N/d)+2Nr_C(y)-2yR(y)-R(y)^2-R(N)\log N+\int_1^N\frac{R(t)}t\,dt.$$
--   Moreover,
--   $$|A_C(N)|\le1+2\sum_{1\le d\le y}\Lambda(d)|R(N/d)|+|2Nr_C(y)-2yR(y)|+R(y)^2+|R(N)|\log N+\int_1^N\frac{|R(t)|}t\,dt.$$
--   These unconditional formulas reduce estimates for the centered prime convolution to precise prime-counting and first-Mertens errors. They retain the square-root endpoint and the constant correction.
-- source:
--   O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 6, https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Compare the corrected identity in https://github.com/gersh/ternary-goldbach-lean/blob/27df23af6a712895f22204d0d81102baa74f0ebe/MathExtras/NumberTheory/Mertens/RamareCorrectedBridge.lean. The present proof derives the symmetric hyperbola formula from our checked asymmetric formula, then uses Mathlib Abel summation. Written by Codex.

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem centered_prime_convolution_sqrt_certificate  (N : ℕ) (C : ℝ) (hN : 1 ≤ N) :
    let y : ℝ := Real.sqrt (N : ℝ)
    let R : ℝ → ℝ := fun t => Chebyshev.psi t - t
    let r : ℝ := (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d / (d : ℝ)) - Real.log y + C / 2
    ((∑ n ∈ Icc 1 N, ((vonMangoldt * vonMangoldt) n -
      vonMangoldt n * Real.log (n : ℝ) + C)) =
      -1 + 2 * (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d * R ((N : ℝ) / (d : ℝ))) +
      2 * (N : ℝ) * r - 2 * y * R y - (R y) ^ 2 -
      R (N : ℝ) * Real.log (N : ℝ) +
      ∫ t in (1 : ℝ)..(N : ℝ), R t / t) ∧
    (|∑ n ∈ Icc 1 N, ((vonMangoldt * vonMangoldt) n -
      vonMangoldt n * Real.log (n : ℝ) + C)| ≤
      1 + 2 * (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d * |R ((N : ℝ) / (d : ℝ))|) +
      |2 * (N : ℝ) * r - 2 * y * R y| + (R y) ^ 2 +
      |R (N : ℝ)| * Real.log (N : ℝ) +
      ∫ t in (1 : ℝ)..(N : ℝ), |R t| / t) := by sorry

end Helfgott
