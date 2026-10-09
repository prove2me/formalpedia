-- Prove2me | Theorems.Thm_Helfgott_moebius_reciprocal_el_marraki_bound
-- name    : Helfgott.moebius_reciprocal_el_marraki_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T19:26:07.309575+00:00
-- url     : https://prove2.me/theorems/28f844e6-7b1e-4f25-bbd7-6539566e251f
-- title:
--   Complete El Marraki bound for the reciprocal Mobius sum
-- statement:
--   Let $M(t)=\sum_{1\le d\le\lfloor t\rfloor}\mu(d)$ and $m(x)=\sum_{1\le d\le\lfloor x\rfloor}\mu(d)/d$. For every real $x\ge1$, $$|m(x)|\le\frac{|M(x)|}{x}+\frac1x\int_1^x\frac{|M(t)|}{t}\,dt+\frac{\log x}{x}.$$ The full integral identity, fractional-part kernel bounds and every required integrability statement are proved. No bound on M is assumed.
-- source:
--   O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1, https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Complete analytic input to El Marraki conversion, toward the quantitative Mobius cancellation used in Helfgott minor-arc bounds. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem moebius_reciprocal_el_marraki_bound  (x : ℝ) (hx : 1 ≤ x) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ)| / x +
        (∫ t in (1 : ℝ)..x,
          |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) / x +
        Real.log x / x := by sorry

end Helfgott
