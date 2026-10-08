-- Prove2me | Theorems.Thm_Helfgott_regularized_primitive_trivial_zero_order_le_one
-- name    : Helfgott.regularized_primitive_trivial_zero_order_le_one
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T03:01:10.007348+00:00
-- url     : https://prove2.me/theorems/e92c54c4-d904-4ccd-b26f-8a27b4c4ca6e
-- title:
--   The origin has multiplicity at most one for every regularized primitive Dirichlet L-function
-- statement:
--   Let $\chi$ be a primitive Dirichlet character of conductor $q\ge1$. Put $H(s)=L(s,\chi)$ for a nonprincipal character, and use the analytic pole-removed zeta function for the primitive principal character. Then the analytic multiplicity at the origin satisfies $$m_H(0)\le1.$$ For an even nonprincipal primitive character the trivial zero at zero is simple; for an odd character and the regularized principal character the value is nonzero. This isolates the trivial zero from critical-line location certificates in the Goldbach major-arc estimates.
-- source:
--   Mathlib Dirichlet functional equation, nonvanishing at one, reciprocal real gamma factor and analytic orders. Written by Codex.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Analytic.Order
open scoped Classical

namespace Helfgott
theorem regularized_primitive_trivial_zero_order_le_one (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) :
    analyticOrderNatAt (if χ=1 then DirichletCharacter.LFunctionTrivChar₁ 1 else χ.LFunction)
      (0 : ℂ)≤1 := by sorry
end Helfgott
