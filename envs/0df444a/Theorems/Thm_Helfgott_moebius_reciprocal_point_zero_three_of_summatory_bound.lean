-- Prove2me | Theorems.Thm_Helfgott_moebius_reciprocal_point_zero_three_of_summatory_bound
-- name    : Helfgott.moebius_reciprocal_point_zero_three_of_summatory_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T19:55:43.645233+00:00
-- url     : https://prove2.me/theorems/0a31f6fc-66f5-497a-b247-7e49e2215cc1
-- title:
--   Explicit reciprocal Mobius decay from a summatory bound and a finite initial integral
-- statement:
--   Let $M(t)=\sum_{1\le n\le\lfloor t\rfloor}\mu(n)$ and $m(x)=\sum_{1\le n\le\lfloor x\rfloor}\mu(n)/n$. Suppose $x\ge1\,200\,000$, that
--   $$|M(t)|\le\frac{(0.013\log t-0.118)t}{(\log t)^2}\quad(1\,078\,853\le t\le x),$$
--   and that
--   $$\int_1^{1\,078\,853}\frac{|M(t)|}{t}\,dt\le303.$$
--   Then
--   $$|m(x)|\le\frac{0.03}{\log x}.$$
--   The conclusion follows by a complete quantitative El Marraki conversion with exact real cutoffs. The summatory estimate and the finite initial integral are explicit hypotheses and remain separate proof obligations.
-- source:
--   Quantitative specialization of El Marraki conversion; summatory constants and summatory threshold from O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), Theorem 1.1 and section 9, https://www.impan.pl/shop/en/publication/transaction/download/product/82991. The initial bound 303 is an explicit separate hypothesis. The 1200000 threshold and all logarithmic error estimates are independently proved. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem moebius_reciprocal_point_zero_three_of_summatory_bound  (x : ℝ)
    (hx : 1200000 ≤ x)
    (hM : ∀ t ∈ Set.Icc (1078853 : ℝ) x,
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| ≤
        ((13 / 1000) * Real.log t - 118 / 1000) * t / Real.log t ^ 2)
    (hinitial : (∫ t in (1 : ℝ)..(1078853 : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ 303) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (3 / 100) / Real.log x := by sorry

end Helfgott
