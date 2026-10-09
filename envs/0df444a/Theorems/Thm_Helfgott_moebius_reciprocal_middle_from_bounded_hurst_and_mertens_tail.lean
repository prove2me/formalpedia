-- Prove2me | Theorems.Thm_Helfgott_moebius_reciprocal_middle_from_bounded_hurst_and_mertens_tail
-- name    : Helfgott.moebius_reciprocal_middle_from_bounded_hurst_and_mertens_tail
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T03:07:34.984366+00:00
-- url     : https://prove2.me/theorems/89403908-aaa0-4a0a-841e-f01ced1abbea
-- title:
--   Middle reciprocal Mobius range from bounded Hurst and coarse Mertens tail
-- statement:
--   Let $M(n)=\sum_{d=1}^n\mu(d)$, where $\mu$ is the Mobius function. Suppose
--   $$|M(n)|\le0.571\sqrt n\qquad(80000\le n\le10^{16}),$$
--   $$|M(n)|\le\frac n{4345}\qquad(n\ge10^{16}).$$
--   Then every real $x$ in the middle range $1200000\le x\le10^{28}$ satisfies
--   $$\left|\sum_{d\le\lfloor x\rfloor}\frac{\mu(d)}d\right|\le\frac{0.03}{\log x}.$$
--   The initial integral through $1078853$ is discharged by an independently accepted finite proof. This joins the accepted finite reciprocal window to the separate prime-error-based high tail, using the same bounded Hurst and coarse Mertens inputs as the CDEM bootstrap. The two stated inputs are explicit assumptions; no new bounded computation is needed by this middle-range conversion.
-- source:
--   Independent middle-range El Marraki conversion in the framework of O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem moebius_reciprocal_middle_from_bounded_hurst_and_mertens_tail
    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤
        (571 / 1000 : ℝ) * Real.sqrt k)
    (hTail : ∀ k : ℕ, 10 ^ 16 ≤ k →
      |∑ d ∈ Icc 1 k, ((moebius d : ℤ) : ℝ)| ≤ (k : ℝ) / 4345)
    (x : ℝ) (hx : 1200000 ≤ x) (hhi : x ≤ 10 ^ 28) :
    |∑ d ∈ Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (3 / 100) / Real.log x := by sorry

end Helfgott
