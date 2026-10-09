-- Prove2me | Theorems.Thm_Helfgott_moebius_logarithmic_floor_integral_certificate
-- name    : Helfgott.moebius_logarithmic_floor_integral_certificate
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T19:16:59.79943+00:00
-- url     : https://prove2.me/theorems/d4bf695e-8dcc-4c71-9abd-8a0a71ee395b
-- title:
--   Complete continuous logarithmic Mobius kernel with interval integrability
-- statement:
--   Let $M(t)=\sum_{1\le d\le\lfloor t\rfloor}\mu(d)$. For every real $x\ge1$, the function $t\mapsto\lfloor x/t\rfloor M(t)/t$ is interval integrable on $[1,x]$, and $$\int_1^x\lfloor x/t\rfloor M(t)\,\frac{dt}{t}=\log x.$$ All cutoffs and endpoint conventions are exact. There are no analytic or numerical hypotheses.
-- source:
--   O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, equation (9.2), https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Complete analytic input to El Marraki conversion, toward the quantitative Mobius cancellation used in Helfgott minor-arc bounds. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem moebius_logarithmic_floor_integral_certificate  (x : ℝ) (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t)
      volume 1 x ∧
    (∫ t in (1 : ℝ)..x,
      (⌊x / t⌋₊ : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)) / t) =
      Real.log x := by sorry

end Helfgott
