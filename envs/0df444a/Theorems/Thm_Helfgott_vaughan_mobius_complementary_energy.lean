-- Prove2me | Theorems.Thm_Helfgott_vaughan_mobius_complementary_energy
-- name    : Helfgott.vaughan_mobius_complementary_energy
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T20:59:43.016794+00:00
-- url     : https://prove2.me/theorems/ad31f0a7-cccc-4b8a-ab80-16e0e38a88bc
-- title:
--   Unconditional Vaughan coefficient energy over complementary divisor ranges
-- statement:
--   For natural numbers $U,A,B$ with $U\ge1$ and $A\le B\le2A$, define
--   $$b_U(m)=\sum_{\substack{d\mid m\\d>U}}\mu(d),\qquad Y=\left\lfloor\frac B{U+1}\right\rfloor,\qquad Z=\sum_{n=1}^{\infty}n^{-3/2}.$$
--   Then
--   $$\sum_{A<m\le B}b_U(m)^2\le\frac{\pi^4}{36}(B-A)\sum_{s=1}^{Y}\frac1s+\frac{127}{25}Z^3\frac{B\sqrt B}{U+1}.$$
--   The harmonic sum is zero when $Y=0$. This unconditional estimate uses the shorter complementary divisor ranges and avoids the $U^2$ error from direct divisor-pair counting. Its main term is $O((B-A)(1+\log Y))$.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.1, https://arxiv.org/abs/1205.5252. Reuses fully proved density and cutoff integral reductions from Apache 2.0 Prove2Me submissions by raresbuhai. The unconditional coprime Mobius bound, sigma-weight transfer and uniform energy assembly were formalized in this project.

import Definitions.Def_Helfgott_VaughanData
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Real
open Finset ArithmeticFunction Helfgott
open scoped BigOperators

theorem Helfgott.vaughan_mobius_complementary_energy (U A B : ℕ)
    (hU : 1 ≤ U) (hAB : A ≤ B) (hhalf : B ≤ 2*A) :
    (∑ m ∈ Ioc A B,
      ((arithmeticTail U (moebius:ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) ≤
      (Real.pi^4/36)*((B:ℝ)-A)*(∑ s ∈ Icc 1 (B/(U+1)), 1/(s:ℝ))+
      (127/25:ℝ)*(∑' d:ℕ, 1/((d:ℝ)*Real.sqrt (d:ℝ)))^3*
        ((B:ℝ)*Real.sqrt (B:ℝ)/(U+1:ℕ)) := by sorry
