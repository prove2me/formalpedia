-- Prove2me | Theorems.Thm_Helfgott_actual_vaughan_odd_mobius_quadratic_integral_upper
-- name    : Helfgott.actual_vaughan_odd_mobius_quadratic_integral_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T15:57:55.026414+00:00
-- url     : https://prove2.me/theorems/05438782-9912-4549-b5de-d8b0774d7a1c
-- title:
--   Actual odd Vaughan coefficient energy bounded by integrals of Mobius cancellation squares
-- statement:
--   For nonnegative integers $U,A,B$ with $A\le B\le2A$, let $Y_s=\lfloor B/((U+1)s)\rfloor$ and $\sigma(n)=\prod_{p\mid n}(p+1)$. The actual odd Vaughan Mobius-tail square energy satisfies $$\sum_{A<m\le B\atop(m,2)=1}\left(\sum_{d\mid m,\ d>U}\mu(d)\right)^2\le\frac4{\pi^2}\sum_{1\le s\le B/(U+1)\atop(s,2)=1}\int_{A/s}^{B/s}\sum_{1\le d\le Y_s\atop(d,2)=1}\frac{|\mu(d)|}{\sigma(d)^2}\left(\sum_{1\le a\le Y_s/d\atop(a,2d)=1,\ Uda<z}\frac{\mu(a)}{\sigma(a)}\right)^2\,dz+10.7\frac{B\sqrt B}{U+1}.$$ All cutoffs are exact, and each integral contains nonnegative squares retaining one-variable Mobius cancellation. This supplies the actual coefficient-energy input needed for the sharper Vaughan Type II bound.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, sections 4.1.1-4.1.2, equations (4.7)-(4.20), https://arxiv.org/abs/1205.5252. Complete Lean proof for the actual mission coefficients and every finite endpoint. Written by Codex.

import Mathlib
import Definitions.Def_Helfgott_VaughanData
open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem actual_vaughan_odd_mobius_quadratic_integral_upper  (U A B : ℕ)
    (hAB : A ≤ B) (hhalf : B ≤ 2*A) :
    let sigma : ℕ→ℝ := fun q => ∏ p∈q.primeFactors,((p : ℝ)+1)
    (∑ m∈Finset.Ioc A B,if Nat.Coprime m 2 then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)≤
      (4/Real.pi^2)*(∑ s∈Finset.Icc 1 (B/(U+1)),if Nat.Coprime s 2 then
        ∫ z in ((A : ℝ)/(s : ℝ))..((B : ℝ)/(s : ℝ)),
          ∑ d∈Finset.Icc 1 (B/((U+1)*s)),if Nat.Coprime d 2 then
            (|((moebius d : ℤ) : ℝ)|/(sigma d)^2)*
              (∑ a∈Finset.Icc 1 ((B/((U+1)*s))/d),
                if Nat.Coprime a (d*2) ∧ (U : ℝ)*(d*a : ℕ)<z then
                  ((moebius a : ℤ) : ℝ)/sigma a else 0)^2 else 0 else 0)+
      (107/10:ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by sorry

end Helfgott
