-- Prove2me | Theorems.Thm_Helfgott_mobius_sigma_coprime_real_two_power_rankin_upper
-- name    : Helfgott.mobius_sigma_coprime_real_two_power_rankin_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:59:03.209173+00:00
-- url     : https://prove2.me/theorems/84efd6f5-fdb9-4691-a551-5d32876af235
-- title:
--   Exact real-cutoff two-power coprime Mobius transfer
-- statement:
--   The actual coprime Mobius-over-sigma sum at the exact real cutoff floor(X) is bounded by a*(L/X)^(1-s)*R_q(s)+b*(T/X)^(1-t)*R_q(t), for X>=1, L,T,a,b>=0 and half-to-one exponents, assuming the displayed two-power envelope for the ordinary Mobius reciprocal sum throughout [1,X]. R_q is the sharp single zeta quotient times its exact prime factors. Every nested floor transfer is exact; no natural-quotient factor is lost.
-- source:
--   Exact real-floor convolution and coprime Euler-product estimates toward the Helfgott Type II minor-arc proof. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott
theorem mobius_sigma_coprime_real_two_power_rankin_upper
    (q : ℕ) (X L T a b s t : ℝ)
    (hq : 1 ≤ q) (hX : 1 ≤ X) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1)
    (hM : ∀ z : ℝ, 1 ≤ z → z ≤ X →
      |∑ r∈Icc 1 ⌊z⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        a*(L/z)^(1-s)+b*(T/z)^(1-t)) :
    let R : ℝ → ℝ := fun u => (((∑' n : ℕ,(n : ℝ)^(-u-1))*(∑' n : ℕ,(n : ℝ)^(-2*u-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ))) *
      (∏ p∈q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u)))
    |∑ r∈Icc 1 ⌊X⌋₊, if Nat.Coprime r q then
      ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors, ((p : ℝ)+1)) else 0| ≤
      a*(L/X)^(1-s)*R s +
        b*(T/X)^(1-t)*R t := by sorry
end Helfgott
