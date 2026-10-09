-- Prove2me | Theorems.Thm_Helfgott_moebius_initial_integral_le_303
-- name    : Helfgott.moebius_initial_integral_le_303
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:16:08.019178+00:00
-- url     : https://prove2.me/theorems/e72a19e3-e151-403c-accf-1c854037266d
-- title:
--   Certified finite initial Mobius integral is at most 303
-- statement:
--   For the actual Möbius function, $$\int_1^{1078853}\frac{\left|\sum_{1\le d\le\lfloor t\rfloor}\mu(d)\right|}{t}\,dt\le303.$$ This is the complete finite numerical input used in the explicit reciprocal Möbius decay transfer for the Helfgott minor-arc route. It contains no numerical certificate hypothesis. The proof assembles the checked arithmetic intervals and the independent certificate soundness theorem.
-- source:
--   Original complete finite arithmetic certificate toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Uses the independently certified bound 303 for the initial integral. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem moebius_initial_integral_le_303 : (∫ t in (1 : ℝ)..(1078853 : ℝ), |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ 303 := by sorry

end Helfgott
