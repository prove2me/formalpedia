-- Prove2me | Theorems.Thm_Helfgott_mobius_sigma_coprime_real_two_power_energy_upper
-- name    : Helfgott.mobius_sigma_coprime_real_two_power_energy_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:43:23.463403+00:00
-- url     : https://prove2.me/theorems/4ff284c0-95ee-4d29-8f13-e445bfb19c45
-- title:
--   Exact real-cutoff divisor energy from two reciprocal Mobius powers
-- statement:
--   Let q be a positive integer, X>=1, L,T,a,b>=0 and 1/2<s,t<=1. Assume abs(m(z))<=a*(L/z)^(1-s)+b*(T/z)^(1-t) for every 1<=z<=X, where m(z) is the actual floor-truncated Mobius reciprocal sum. Define R_q(u)=Phi(u+1)*Phi(2u+1)/Phi(3) times the product over p dividing q of (p+1)/(p+1-p*p^(-u)), and C(u,v)=Phi(u+v)*Phi(u+2v)*Phi(2u+v)/(Phi(3)^2*Phi(4)). With P=(L/X)^(1-s) and Z=(T/X)^(1-t), the divisor-weighted square energy of the coprime Mobius-over-sigma sums at the exact real cutoffs X/d is bounded by a^2*P^2*R_q(s)^2*C(s,s)+2*a*b*P*Z*R_q(s)*R_q(t)*C(s,t)+b^2*Z^2*R_q(t)^2*C(t,t). Phi(u) is the positive-integer Dirichlet series, sigma(d)=product_(p|d)(p+1), and the outer weight is abs(mu(d))/sigma(d)^2. The displayed reciprocal envelope remains an explicit hypothesis. Real floor identities are proved exactly, with no extra factor from natural quotient approximation.
-- source:
--   Original exact real-floor positive convolution and coupled Rankin moment transfer for the Helfgott minor-arc Type II coefficient energy. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott
theorem mobius_sigma_coprime_real_two_power_energy_upper
    (q : ℕ) (X L T a b s t : ℝ)
    (hq : 1 ≤ q) (hX : 1 ≤ X) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs0 : 1/2 < s) (hs1 : s ≤ 1)
    (ht0 : 1/2 < t) (ht1 : t ≤ 1)
    (hM : ∀ z : ℝ, 1 ≤ z → z ≤ X →
      |∑ r∈Icc 1 ⌊z⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        a*(L/z)^(1-s)+b*(T/z)^(1-t)) :
    let R : ℝ → ℝ := fun u =>
      (((∑' n : ℕ,(n : ℝ)^(-u-1))*(∑' n : ℕ,(n : ℝ)^(-2*u-1)))/
        (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))) *
        (∏ p∈q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u)))
    let C : ℝ → ℝ → ℝ := fun u v =>
      ((∑' n : ℕ,(n : ℝ)^(-u-v))*(∑' n : ℕ,(n : ℝ)^(-u-2*v))*(∑' n : ℕ,(n : ℝ)^(-2*u-v)))/
        ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ)))
    let P : ℝ := (L/X)^(1-s)
    let Z : ℝ := (T/X)^(1-t)
    (∑ d∈Icc 1 ⌊X⌋₊, if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors, ((p : ℝ)+1))^2 *
        (∑ r∈Icc 1 ⌊X/(d : ℝ)⌋₊, if Nat.Coprime r (d*q) then
          ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors, ((p : ℝ)+1)) else 0)^2 else 0) ≤
      a^2*P^2*(R s)^2*C s s + 2*a*b*P*Z*R s*R t*C s t + b^2*Z^2*(R t)^2*C t t := by sorry
end Helfgott
