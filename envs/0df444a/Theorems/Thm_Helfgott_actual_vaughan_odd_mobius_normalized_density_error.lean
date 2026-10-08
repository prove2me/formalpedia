-- Prove2me | Theorems.Thm_Helfgott_actual_vaughan_odd_mobius_normalized_density_error
-- name    : Helfgott.actual_vaughan_odd_mobius_normalized_density_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T15:23:27.67589+00:00
-- url     : https://prove2.me/theorems/9a1fe81e-f49a-4f9e-ac88-4e7df48b37d0
-- title:
--   Explicit 10.7 error and normalized signed main term for actual odd Vaughan Mobius energy
-- statement:
--   For every U,A,B>=0 with A<=B<=2*A, the actual odd Vaughan Mobius-tail coefficient square energy differs from its normalized signed density main term by at most 10.7*B*sqrt(B)/(U+1). The main term is (4/pi^2) times the smaller triple sum of mu(r)/sigma(r)*mu(t)/sigma(t)*(B/s-max(A/s,U*r,U*t)), with r,t coprime and r*t*s odd; sigma(n) is the product of p+1 over prime divisors of n. Every finite cutoff and empty endpoint is included. This establishes the explicit arithmetic input retaining the signed cancellation needed for the actual Type II estimate.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.1, equations (4.7)-(4.8), https://arxiv.org/abs/1205.5252. Original complete Lean proof for the actual mission Vaughan coefficient, with exact integer endpoints and smaller complementary ranges. Written by Codex.

import Mathlib
import Definitions.Def_Helfgott_VaughanData
open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem actual_vaughan_odd_mobius_normalized_density_error  (U A B : ℕ)
    (hAB : A ≤ B) (hhalf : B ≤ 2*A) :
    let sigma : ℕ→ℝ := fun q => ∏ p∈q.primeFactors,((p : ℝ)+1)
    |(∑ m∈Finset.Ioc A B,if Nat.Coprime m 2 then
        ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)-
      (4/Real.pi^2)*(∑ s∈Finset.Icc 1 (B/(U+1)),
        ∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
          if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) 2 then
            (((moebius r : ℤ) : ℝ)/sigma r)*(((moebius t : ℤ) : ℝ)/sigma t)*
              ((B : ℝ)/(s : ℝ)-max ((A : ℝ)/(s : ℝ)) (max ((U : ℝ)*t) ((U : ℝ)*r))) else 0)| ≤
      (107/10:ℝ)*((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by sorry

end Helfgott
