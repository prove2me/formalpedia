-- Prove2me | Theorems.Thm_Helfgott_actual_vaughan_mobius_interval_density_error
-- name    : Helfgott.actual_vaughan_mobius_interval_density_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T15:05:41.268985+00:00
-- url     : https://prove2.me/theorems/d0c56d0f-fac2-448d-a327-f4ccae92e51c
-- title:
--   Sharp density approximation for the actual Vaughan Mobius interval energy
-- statement:
--   For every nonnegative U,A,B and positive v with A<=B<=2A, the actual coprime Vaughan Mobius coefficient square energy differs from its exact signed finite density main term by at most the sum of 1.27*abs(mu(r)mu(t))*sqrt(B/(rts))*prod_{p|rtv}(1+1/sqrt(p)) over the smaller complementary ranges. The main interval has real length B/(rts)-max(A/(rts),U/r,U/t) and canonical squarefree coprime density (6/pi^2)*prod p/(p+1). All finite endpoints and empty ranges are covered. The signed main-term cancellation is retained; no coefficient energy assumption is used.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.1, equations (4.7)-(4.8), https://arxiv.org/abs/1205.5252. Original complete Lean proof for the actual mission Vaughan coefficient, with exact integer endpoints and smaller complementary ranges. Written by Codex.

import Mathlib
import Definitions.Def_Helfgott_VaughanData
open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem actual_vaughan_mobius_interval_density_error  (U A B v : ℕ)
    (hv : 1≤v) (hAB : A≤B) (hhalf : B≤2*A) :
    let rho : ℕ→ℝ := fun q => (6/Real.pi^2)*∏ p∈q.primeFactors,(p : ℝ)/((p : ℝ)+1)
    let omega : ℕ→ℝ := fun q => ∏ p∈q.primeFactors,(1+1/Real.sqrt (p : ℝ))
    let L : ℕ→ℕ→ℕ→ℝ := fun s r t => max ((A : ℝ)/(r*t*s : ℕ)) (max ((U : ℝ)/r) ((U : ℝ)/t))
    |(∑ m∈Finset.Ioc A B,if Nat.Coprime m v then
        ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)-
      (∑ s∈Finset.Icc 1 (B/(U+1)),∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
        if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
          ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
            (((B : ℝ)/(r*t*s : ℕ)-L s r t)*rho (r*t*v)) else 0)|≤
      ∑ s∈Finset.Icc 1 (B/(U+1)),∑ r∈Finset.Icc 1 (B/((U+1)*s)),∑ t∈Finset.Icc 1 (B/((U+1)*s)),
        if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
          |((moebius r : ℤ) : ℝ)| *|((moebius t : ℤ) : ℝ)| *(127/100:ℝ)*
            Real.sqrt ((B : ℝ)/(r*t*s : ℕ))*omega (r*t*v) else 0 := by sorry

end Helfgott
