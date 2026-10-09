-- Prove2me | Theorems.Thm_Helfgott_centered_prime_convolution_tail_certificate
-- name    : Helfgott.centered_prime_convolution_tail_certificate
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:59:28.729702+00:00
-- url     : https://prove2.me/theorems/79e1f23f-4743-4177-b1c2-1f5dd5622b84
-- title:
--   Centered prime convolution controlled by a normalized prime-error tail
-- statement:
--   Write $R(t)=\psi(t)-t$, where $\psi$ is the Chebyshev function. Suppose $R(t)/t^2$ is integrable on $(1,\infty)$, and define
--   $$C=-2\left(1+\int_1^\infty R(t)/t^2\,dt\right).$$
--   For an integer $N\ge1$, put $y=\sqrt N$, $r_C(y)=\sum_{1\le d\le y}\Lambda(d)/d-\log y+C/2$, and
--   $$A_C(N)=\sum_{n=1}^N\big((\Lambda*\Lambda)(n)-\Lambda(n)\log n+C\big).$$
--   Then the combined endpoint correction has the exact form
--   $$2Nr_C(y)-2yR(y)=-2N\int_y^\infty R(t)/t^2\,dt,$$
--   and
--   $$|A_C(N)|\le1+2\sum_{1\le d\le y}\Lambda(d)|R(N/d)|+2N\int_y^\infty|R(t)|/t^2\,dt+R(y)^2+|R(N)|\log N+\int_1^N|R(t)|/t\,dt.$$
--   This retains cancellation between the first-Mertens remainder and its endpoint correction. Quantitative bounds for the Chebyshev error, and hence its tail integrability, remain explicit subsequent obligations. The centering constant is defined by the displayed integral; no numerical value for it is assumed.
-- source:
--   Independent Abel-summation refinement of the centered prime-convolution identity used in O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Written by Codex.

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

theorem centered_prime_convolution_tail_certificate  (N : ℕ) (hN : 1 ≤ N)
    (hR : IntegrableOn (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2)
      (Set.Ioi 1)) :
    let C : ℝ := -2 * (1 + ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2)
    let y : ℝ := Real.sqrt (N : ℝ)
    let R : ℝ → ℝ := fun t => Chebyshev.psi t - t
    let r : ℝ := (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d / (d : ℝ)) - Real.log y + C / 2
    (2 * (N : ℝ) * r - 2 * y * R y =
      -2 * (N : ℝ) * ∫ t in Set.Ioi y, R t / t ^ 2) ∧
    (|∑ n ∈ Icc 1 N, ((vonMangoldt * vonMangoldt) n -
      vonMangoldt n * Real.log (n : ℝ) + C)| ≤
      1 + 2 * (∑ d ∈ Icc 1 ⌊y⌋₊, vonMangoldt d * |R ((N : ℝ) / (d : ℝ))|) +
      2 * (N : ℝ) * (∫ t in Set.Ioi y, |R t| / t ^ 2) + (R y) ^ 2 +
      |R (N : ℝ)| * Real.log (N : ℝ) +
      ∫ t in (1 : ℝ)..(N : ℝ), |R t| / t) := by sorry

end Helfgott
