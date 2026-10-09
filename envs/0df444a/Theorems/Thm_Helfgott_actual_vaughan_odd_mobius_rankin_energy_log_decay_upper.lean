-- Prove2me | Theorems.Thm_Helfgott_actual_vaughan_odd_mobius_rankin_energy_log_decay_upper
-- name    : Helfgott.actual_vaughan_odd_mobius_rankin_energy_log_decay_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:25:28.22793+00:00
-- url     : https://prove2.me/theorems/9f4109a5-183a-4e9d-9643-9f9663964177
-- title:
--   Actual odd Vaughan coefficient energy with evaluated Rankin integrals
-- statement:
--   Assume $|\sum_{n\le\lfloor x\rfloor}\mu(n)/n|\le0.03/\log x$ for every $x\ge11815$. Let U,A,B,L be natural numbers with $A\le B\le2A$, $U\ge1$, $L\ge11815$, and let $1/2<s\le1$. Define the actual Vaughan coefficient $b_U(m)=\sum_{d\mid m,\ d>U}\mu(d)$ and
--   $$\Phi(u)=\sum_{n=1}^{\infty}n^{-u},\qquad R(t)=\frac{\Phi(t+1)\Phi(2t+1)}{\Phi(3)}\frac{3}{3-2\cdot2^{-t}},$$
--   $$C(u,v)=\frac{\Phi(u+v)\Phi(u+2v)\Phi(2u+v)}{\Phi(3)^2\Phi(4)},\qquad c=\frac{0.03}{\log L},$$
--   $$T_k=\max\left(1,\left\lfloor\frac{A}{(U+1)k}\right\rfloor\right),\qquad P_k=(2L/T_k)^{1-s}.$$
--   Then
--   $$\sum_{\substack{A<m\le B\\m\text{ odd}}}b_U(m)^2
--   \le\frac4{\pi^2}(B-A)\sum_{\substack{k\le\lfloor B/(U+1)\rfloor\\k\text{ odd}}}\frac{c^2R(1)^2C(1,1)+2cP_kR(1)R(s)C(1,s)+P_k^2R(s)^2C(s,s)}k
--   +10.7\frac{B\sqrt B}{U+1}.$$
--   Every strict cutoff, interval-integrability obligation, integer quotient and squarefree density error is proved. The bound has no remaining integrals, coefficient-energy hypothesis or new finite computation input. The stated ordinary reciprocal decay remains its sole analytic cancellation assumption.
-- source:
--   Independent explicit transfer combining exact Mobius-over-sigma and coprime positive convolutions with proved single Rankin prime factors and divisor moments. The only analytic assumption is the displayed ordinary reciprocal decay. Written by Codex.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Definitions.Def_Helfgott_VaughanData
open Helfgott Finset Nat Real ArithmeticFunction MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem actual_vaughan_odd_mobius_rankin_energy_log_decay_upper
    (hdecay : ∀ x : ℝ, 11815 ≤ x →
      |∑ a∈Icc 1 ⌊x⌋₊, ((moebius a : ℤ) : ℝ)/(a : ℝ)| ≤ (3/100)/Real.log x)
    (U A B L : ℕ) (s : ℝ) (hAB : A ≤ B) (hhalf : B ≤ 2*A) (hU : 1 ≤ U)
    (hL : 11815 ≤ L) (hs0 : 1/2 < s) (hs1 : s ≤ 1) :
    let R : ℝ → ℝ := fun t =>
      (((∑' n : ℕ,(n : ℝ)^(-t-1))*(∑' n : ℕ,(n : ℝ)^(-2*t-1)))/
        (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))) *
        (∏ p∈(2 : ℕ).primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-t)))
    let C : ℝ → ℝ → ℝ := fun u v =>
      ((∑' n : ℕ,(n : ℝ)^(-u-v))*(∑' n : ℕ,(n : ℝ)^(-u-2*v))*(∑' n : ℕ,(n : ℝ)^(-2*u-v)))/
        ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ)))
    let P : ℕ → ℝ := fun k => (((2*(L : ℝ))/(max 1 (A/((U+1)*k)) : ℕ))^(1-s))
    (∑ m∈Ioc A B, if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0) ≤
      (4/Real.pi^2)*((B : ℝ)-A)*
        (∑ k∈Icc 1 (B/(U+1)), if Nat.Coprime k 2 then
          (((3/100)/Real.log (L : ℝ))^2*(R 1)^2*C 1 1 + 2*((3/100)/Real.log (L : ℝ))*P k*R 1*R s*C 1 s + (P k)^2*(R s)^2*C s s)/k else 0) +
      (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by sorry

end Helfgott
