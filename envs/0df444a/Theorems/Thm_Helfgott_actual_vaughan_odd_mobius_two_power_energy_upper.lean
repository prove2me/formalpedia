-- Prove2me | Theorems.Thm_Helfgott_actual_vaughan_odd_mobius_two_power_energy_upper
-- name    : Helfgott.actual_vaughan_odd_mobius_two_power_energy_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:07:34.656084+00:00
-- url     : https://prove2.me/theorems/388f1910-bfdb-4861-94ac-9ad4b8a8f757
-- title:
--   Actual odd Vaughan coefficient energy with sharp two-power cancellation
-- statement:
--   Let $U,A,B$ be natural numbers with $U\ge1$ and $A\le B\le2A$. Let $X\ge\lfloor B/(U+1)\rfloor$, $L,T,a,b\ge0$, and $1/2<s,t\le1$. Write $m(v)=\sum_{n\le\lfloor v\rfloor}\mu(n)/n$, and assume
--   $$|m(v)|\le a(L/v)^{1-s}+b(T/v)^{1-t}\qquad(1\le v\le X).$$
--   Put $\Phi(u)=\sum_{n\ge1}n^{-u}$,
--   $$R(u)=\frac{\Phi(u+1)\Phi(2u+1)}{\Phi(3)}\frac3{3-2\cdot2^{-u}},$$
--   $$C(u,v)=\frac{\Phi(u+v)\Phi(u+2v)\Phi(2u+v)}{\Phi(3)^2\Phi(4)}\left(1+\frac{2^{-u-v}}{(3/2-2^{-u})(3/2-2^{-v})}\right)^{-1}.$$
--   For $N_k=\max(1,\lfloor A/((U+1)k)\rfloor)$ set $P_k=(L/N_k)^{1-s}$ and $Z_k=(T/N_k)^{1-t}$. The actual Vaughan coefficient $b_U(m)=\sum_{d\mid m,\,d>U}\mu(d)$ satisfies
--   $$\sum_{\substack{A<m\le B\\m\ {\rm odd}}}b_U(m)^2\le\frac4{\pi^2}(B-A)\sum_{\substack{1\le k\le\lfloor B/(U+1)\rfloor\\k\ {\rm odd}}}\frac{a^2P_k^2R(s)^2C(s,s)+2abP_kZ_kR(s)R(t)C(s,t)+b^2Z_k^2R(t)^2C(t,t)}k+10.7\frac{B\sqrt B}{U+1}.$$
--   This evaluates every cancellation integral in the Vaughan energy reduction, using exact real cutoffs and retaining the coupled Euler factor for the excluded prime $2$. The displayed ordinary reciprocal envelope is the sole cancellation hypothesis.
-- source:
--   Exact two-power cancellation transfer, strict-cutoff evaluation and excluded-prime Rankin moments toward Helfgott Type II estimates. Written by Codex.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Definitions.Def_Helfgott_VaughanData
open Helfgott Finset Nat Real ArithmeticFunction MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott
theorem actual_vaughan_odd_mobius_two_power_energy_upper
    (U A B : ℕ) (X L T a b s t : ℝ)
    (hAB : A ≤ B) (hhalf : B ≤ 2*A) (hU : 1 ≤ U) (hYX : (B/(U+1) : ℕ) ≤ X)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs0 : 1/2 < s) (hs1 : s ≤ 1) (ht0 : 1/2 < t) (ht1 : t ≤ 1)
    (hM : ∀ v : ℝ, 1 ≤ v → v ≤ X →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        a*(L/v)^(1-s)+b*(T/v)^(1-t)) :
    let R : ℝ → ℝ := fun u =>
      (((∑' n : ℕ,(n : ℝ)^(-u-1))*(∑' n : ℕ,(n : ℝ)^(-2*u-1)))/
        (∑' n : ℕ,(n : ℝ)^(-3 : ℝ))) *
        (∏ p∈(2 : ℕ).primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u)))
    let C : ℝ → ℝ → ℝ := fun u v =>
      ((∑' n : ℕ,(n : ℝ)^(-u-v))*(∑' n : ℕ,(n : ℝ)^(-u-2*v))*(∑' n : ℕ,(n : ℝ)^(-2*u-v)))/
        ((∑' n : ℕ,(n : ℝ)^(-3 : ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4 : ℝ))) /
          (∏ p∈(2 : ℕ).primeFactors,(1+(p : ℝ)^(-u-v)/
            ((1-(p : ℝ)^(-u)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-v)+(p : ℝ)^(-1:ℝ)))))
    let P : ℕ → ℝ := fun k => (L/(max 1 (A/((U+1)*k)) : ℕ))^(1-s)
    let Z : ℕ → ℝ := fun k => (T/(max 1 (A/((U+1)*k)) : ℕ))^(1-t)
    (∑ m∈Ioc A B, if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0) ≤
      (4/Real.pi^2)*((B : ℝ)-A)*
        (∑ k∈Icc 1 (B/(U+1)), if Nat.Coprime k 2 then
          (a^2*(P k)^2*(R s)^2*C s s + 2*a*b*(P k)*(Z k)*R s*R t*C s t +
            b^2*(Z k)^2*(R t)^2*C t t)/k else 0) +
      (107/10 : ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by sorry
end Helfgott
