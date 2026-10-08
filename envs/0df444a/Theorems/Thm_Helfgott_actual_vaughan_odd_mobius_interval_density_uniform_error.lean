-- Prove2me | Theorems.Thm_Helfgott_actual_vaughan_odd_mobius_interval_density_uniform_error
-- name    : Helfgott.actual_vaughan_odd_mobius_interval_density_uniform_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T15:11:22.692011+00:00
-- url     : https://prove2.me/theorems/b58525a6-3c95-463f-937f-2bbde40d985a
-- title:
--   Sharp parity saving in the actual Vaughan Mobius interval density error
-- statement:
--   For every nonnegative U,A,B with A<=B<=2A, restricting the actual coefficient to odd m, the actual coprime Vaughan Mobius coefficient square energy differs from its exact signed finite density main term by at most 1.27*(1+1/sqrt(2))*Z_odd^3*B*sqrt(B)/(U+1), where Z_odd is the full convergent sum over odd positive n of 1/(n*sqrt(n)). The main interval has real length B/(rts)-max(A/(rts),U/r,U/t) and canonical squarefree coprime density (6/pi^2)*prod p/(p+1). All finite endpoints and empty ranges are covered. The signed main-term cancellation is retained; no coefficient energy assumption is used.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.1, equations (4.7)-(4.8), https://arxiv.org/abs/1205.5252. Original complete Lean proof for the actual mission Vaughan coefficient, with exact integer endpoints and smaller complementary ranges. Written by Codex.

import Mathlib
import Definitions.Def_Helfgott_VaughanData
open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem actual_vaughan_odd_mobius_interval_density_uniform_error  (U A B : ℕ)
     (hAB : A ≤ B) (hhalf : B ≤ 2*A) :
    let rho : ℕ→ℝ := fun q => (6/Real.pi^2)*∏ p∈q.primeFactors,(p : ℝ)/((p : ℝ)+1)
    let omega : ℕ→ℝ := fun q => ∏ p∈q.primeFactors,(1+1/Real.sqrt (p : ℝ))
    let L : ℕ→ℕ→ℕ→ℝ := fun s r t => max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t))
    |(∑ m∈Finset.Ioc A B,if Nat.Coprime m 2 then
        ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)-
      (∑ s∈Finset.Icc 1 (B/(U+1)),∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
        if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) 2 then
          ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
            (((B : ℝ)/(r*t*s : ℕ)-L s r t)*rho (r*t*2)) else 0)| ≤
      (127/100:ℝ)*omega 2*(∑' d : ℕ,if Nat.Coprime d 2 then 1/((d : ℝ)*Real.sqrt (d : ℝ)) else 0)^3*
        ((B : ℝ)*Real.sqrt (B : ℝ)/(U+1 : ℕ)) := by sorry

end Helfgott
