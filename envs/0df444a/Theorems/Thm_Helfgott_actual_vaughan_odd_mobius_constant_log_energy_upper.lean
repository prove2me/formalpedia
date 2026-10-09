-- Prove2me | Theorems.Thm_Helfgott_actual_vaughan_odd_mobius_constant_log_energy_upper
-- name    : Helfgott.actual_vaughan_odd_mobius_constant_log_energy_upper
-- status  : Open
-- author  : @raresbuhai
-- created : 2026-10-09T05:48:35.427442+00:00
-- url     : https://prove2.me/theorems/482af487-be07-46f3-b289-7ef09bc049f6
-- title:
--   Evaluated Vaughan energy from finite square-root and constant logarithmic cancellation
-- statement:
--   Assume $|m(v)|\le0.03/\log v$ for every $v\ge11815$, where $m(v)=\sum_{n\le\lfloor v\rfloor}\mu(n)/n$. Choose $0<\beta<1/2$ and set $s=1-\beta$, $a=1$, $L=2$, and $b=0.03/\log1200001$.
--
--   For natural numbers $U,A,B$ with $U\ge1$, $A\le B\le2A$, $A\ge1$, and $Y=\lfloor B/(U+1)\rfloor\ge1$, put
--   $$b_U(m)=\sum_{\substack{d\mid m\\d>U}}\mu(d),\quad P=\left(\frac{2L(U+1)}A\right)^{1-s},\quad \Psi_\gamma(Y)=1+\frac{Y^\gamma-1}{2\gamma}.$$
--   Write $\Phi(u)=\sum_{n\ge1}n^{-u}$ and set
--   $$R(u)=\frac{\Phi(u+1)\Phi(2u+1)}{\Phi(3)}\frac3{3-2\cdot2^{-u}},$$
--   $$C(u,v)=\frac{\Phi(u+v)\Phi(u+2v)\Phi(2u+v)}{\Phi(3)^2\Phi(4)}\left(1+\frac{2^{-u-v}}{(3/2-2^{-u})(3/2-2^{-v})}\right)^{-1}.$$
--   Then
--   $$\sum_{\substack{A<m\le B\\m\ {\rm odd}}}b_U(m)^2\le\frac4{\pi^2}(B-A)\left[a^2P^2R(s)^2C(s,s)\Psi_{2(1-s)}(Y)+2abPR(s)R(1)C(s,1)\Psi_{1-s}(Y)+b^2R(1)^2C(1,1)\left(1+\tfrac12\log Y\right)\right]+10.7\frac{B\sqrt B}{U+1}.$$
--   Every cancellation integral and finite outer sum is evaluated. The excluded prime $2$ and half-density of odd indices are retained. The finite square-root estimate through $v<1200001$ is fully discharged by an exact certificate. The all-range logarithmic reciprocal estimate is the sole cancellation hypothesis. The constant contribution grows logarithmically with $Y$, instead of requiring a positive second power exponent.
-- source:
--   Exact two-power cancellation transfer, strict-cutoff evaluation and excluded-prime Rankin moments toward Helfgott Type II estimates. Written by Codex.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Definitions.Def_Helfgott_VaughanData
open Helfgott Finset Nat Real ArithmeticFunction MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott
theorem actual_vaughan_odd_mobius_constant_log_energy_upper
    (hdecay : ∀ v : ℝ, 11815 ≤ v →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤ (3/100)/Real.log v)
    (U A B : ℕ) (beta : ℝ)
    (hA : 1 ≤ A) (hY : 1 ≤ B/(U+1)) (hAB : A ≤ B) (hhalf : B ≤ 2*A) (hU : 1 ≤ U)
    (hb0 : 0 < beta) (hb1 : beta < 1/2) :
    let s : ℝ := 1-beta
    let a : ℝ := 1
    let b : ℝ := (3/100)/Real.log (1200001 : ℝ)
    let L : ℝ := 2
    let R : ℝ → ℝ := fun u =>
      (((∑' n : ℕ,(n : ℝ)^(-u-1))*(∑' n : ℕ,(n : ℝ)^(-2*u-1)))/
        (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))) *
        (∏ p∈(2 : ℕ).primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u)))
    let C : ℝ → ℝ → ℝ := fun u v =>
      ((∑' n : ℕ,(n : ℝ)^(-u-v))*(∑' n : ℕ,(n : ℝ)^(-u-2*v))*(∑' n : ℕ,(n : ℝ)^(-2*u-v)))/
        ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ))) /
          (∏ p∈(2 : ℕ).primeFactors,(1+(p : ℝ)^(-u-v)/
            ((1-(p : ℝ)^(-u)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-v)+(p : ℝ)^(-1:ℝ)))))
    let Y : ℕ := B/(U+1)
    let Psi : ℝ → ℝ := fun gamma => 1+((Y : ℝ)^gamma-1)/(2*gamma)
    let P : ℝ := (2*L*(U+1 : ℕ)/A)^(1-s)
    (∑ m∈Ioc A B,if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0) ≤
      (4/Real.pi^2)*((B : ℝ)-A)*
        (a^2*P^2*(R s)^2*C s s*Psi (2*(1-s)) +
          2*a*b*P*R s*R 1*C s 1*Psi (1-s) +
          b^2*(R 1)^2*C 1 1*(1+Real.log (Y : ℝ)/2)) +
        (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by sorry
end Helfgott
