-- Prove2me | Theorems.Thm_Helfgott_rankin_sharp_coprime_coupled_weight_excluded_upper
-- name    : Helfgott.rankin_sharp_coprime_coupled_weight_excluded_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:59:45.772987+00:00
-- url     : https://prove2.me/theorems/636254a0-f861-4a5b-9f15-aabeaa8c6a45
-- title:
--   Coupled Rankin moment retaining every excluded prime
-- statement:
--   For half-to-one exponents s,t with s+t>1, the actual coprime divisor moment of abs(mu(d))/sigma(d)^2 times d^(2-s-t)*J_(dq)(s)*J_(dq)(t) is at most J_q(s)*J_q(t)*C(s,t)/H_q(s,t). C is the coupled zeta quotient, J the exact sharp single prime factor, and H the positive product of the excluded coupled local factors over primes dividing q. Coprimality is retained in both the finite sum and the complete Euler-product argument.
-- source:
--   Exact real-floor convolution and coprime Euler-product estimates toward the Helfgott Type II minor-arc proof. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott
theorem rankin_sharp_coprime_coupled_weight_excluded_upper (q D : ℕ) (s t : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    let J : ℕ → ℝ → ℝ := fun n u =>
      ∏ p∈n.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u))
    let H : ℝ := ∏ p∈q.primeFactors,(1+(p : ℝ)^(-s-t)/
      ((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))))
    (∑ d∈Icc 1 D,if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2*
        (d : ℝ)^(2-s-t)*J (d*q) s*J (d*q) t else 0) ≤
      J q s*J q t *
        ((((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
          ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))))/H) := by sorry
end Helfgott
