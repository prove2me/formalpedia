-- Prove2me | Theorems.Thm_Helfgott_actual_vaughan_odd_mobius_two_power_log_decay_upper
-- name    : Helfgott.actual_vaughan_odd_mobius_two_power_log_decay_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:13:59.828247+00:00
-- url     : https://prove2.me/theorems/0f98458b-2169-4cfb-8d13-f48a7a7747c9
-- title:
--   Actual odd Vaughan two-power energy from a closed finite Mobius certificate
-- statement:
--   Assume $|m(v)|\le0.03/\log v$ for every $v\ge11815$, where $m(v)=\sum_{n\le\lfloor v\rfloor}\mu(n)/n$. Let $U,A,B$ be natural numbers satisfying $U\ge1$, $A\le B\le2A$ and $X:=\lfloor B/(U+1)\rfloor\ge1200001$. Choose
--   $$0\le\beta<\tfrac12,\qquad\frac1{\log1200001}\le\delta<\tfrac12.$$
--   Set $s=1-\beta$, $t=1-\delta$, $a=1$, $b=0.03/\log X$, $L=2$, and $T=X$.
--
--   Put $\Phi(u)=\sum_{n\ge1}n^{-u}$,
--   $$R(u)=\frac{\Phi(u+1)\Phi(2u+1)}{\Phi(3)}\frac3{3-2\cdot2^{-u}},$$
--   $$C(u,v)=\frac{\Phi(u+v)\Phi(u+2v)\Phi(2u+v)}{\Phi(3)^2\Phi(4)}\left(1+\frac{2^{-u-v}}{(3/2-2^{-u})(3/2-2^{-v})}\right)^{-1}.$$
--   For $N_k=\max(1,\lfloor A/((U+1)k)\rfloor)$ set $P_k=(L/N_k)^{1-s}$ and $Z_k=(T/N_k)^{1-t}$. The actual Vaughan coefficient $b_U(m)=\sum_{d\mid m,\,d>U}\mu(d)$ satisfies
--   $$\sum_{\substack{A<m\le B\\m\ {\rm odd}}}b_U(m)^2\le\frac4{\pi^2}(B-A)\sum_{\substack{1\le k\le\lfloor B/(U+1)\rfloor\\k\ {\rm odd}}}\frac{a^2P_k^2R(s)^2C(s,s)+2abP_kZ_kR(s)R(t)C(s,t)+b^2Z_k^2R(t)^2C(t,t)}k+10.7\frac{B\sqrt B}{U+1}.$$
--   This evaluates every cancellation integral in the Vaughan energy reduction, using exact real cutoffs and retaining the coupled Euler factor for the excluded prime $2$. The finite estimate $m(v)^2v\le2$ for $1\le v<1200001$ is fully discharged by an independent exact certificate. The all-range logarithmic reciprocal estimate is the sole analytic cancellation hypothesis. No finite square-root assumption remains.
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
theorem actual_vaughan_odd_mobius_two_power_log_decay_upper
    (hdecay : ∀ v : ℝ, 11815 ≤ v →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤ (3/100)/Real.log v)
    (U A B : ℕ) (beta delta : ℝ)
    (hAB : A ≤ B) (hhalf : B ≤ 2*A) (hU : 1 ≤ U)
    (hX : 1200001 ≤ B/(U+1))
    (hb0 : 0 ≤ beta) (hb1 : beta < 1/2) (hd1 : delta < 1/2)
    (hd : 1/Real.log (1200001 : ℝ) ≤ delta) :
    let X : ℝ := (B/(U+1) : ℕ)
    let a : ℝ := 1
    let b : ℝ := (3/100)/Real.log X
    let L : ℝ := 2
    let T : ℝ := X
    let s : ℝ := 1-beta
    let t : ℝ := 1-delta
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
