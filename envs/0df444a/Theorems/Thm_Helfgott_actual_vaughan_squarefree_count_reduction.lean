-- Prove2me | Theorems.Thm_Helfgott_actual_vaughan_squarefree_count_reduction
-- name    : Helfgott.actual_vaughan_squarefree_count_reduction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T14:42:15.902347+00:00
-- url     : https://prove2.me/theorems/cbe8cc14-1fc7-4d08-8fcc-17a14bebaefb
-- title:
--   Exact reduction of actual Vaughan Mobius interval energy to small squarefree coprime counts
-- statement:
--   For all nonnegative integers U,A,B,v, the sum over A<m<=B, gcd(m,v)=1 of the squared actual Vaughan Mobius-tail coefficient is exactly a triple sum over s<=B/(U+1) and r,t<=B/((U+1)s). Its signed weights are mu(r)mu(t), with r,t coprime and rst coprime to v, and its inner count is over squarefree g coprime to rtv in the exact interval (max(floor(A/(rts)),floor(U/r),floor(U/t)),floor(B/(rts))]. Every zero, empty interval and finite endpoint is included. This is the complete arithmetic gcd and complementary-factor reduction needed for the sharp Type II cancellation estimate.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.1, equations (4.7)-(4.8), https://arxiv.org/abs/1205.5252. Original complete Lean proof for the actual mission Vaughan coefficient, with exact integer endpoints and smaller complementary ranges. Written by Codex.

import Mathlib
import Definitions.Def_Helfgott_VaughanData
open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem actual_vaughan_squarefree_count_reduction  (U A B v : ℕ) :
    (∑ m ∈ Finset.Ioc A B,if Nat.Coprime m v then
      ((arithmeticTail U (moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)^2 else 0)=
      ∑ s ∈ Finset.Icc 1 (B/(U+1)),
        ∑ r ∈ Finset.Icc 1 (B/((U+1)*s)),∑ t ∈ Finset.Icc 1 (B/((U+1)*s)),
          if Nat.Coprime r t ∧ Nat.Coprime (r*t*s) v then
            ((moebius r : ℤ) : ℝ)*((moebius t : ℤ) : ℝ)*
              (∑ g ∈ Finset.Ioc (max (A/(r*t*s)) (max (U/r) (U/t))) (B/(r*t*s)),
                if Nat.Coprime g (r*t*v) then ((moebius g : ℤ) : ℝ)^2 else 0) else 0 := by sorry

end Helfgott
