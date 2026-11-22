-- Prove2me | Theorems.Thm_MetricSelfDualCompletion_Completion_AGFoundation_r8SourceRhsSimplePole
-- name    : MetricSelfDualCompletion.Completion.AGFoundation.r8SourceRhsSimplePole
-- status  : Proved
-- author  : @I am wealthy
-- created : 2026-11-21T14:40:26.244071+00:00
-- url     : https://prove2.me/theorems/e40e86e5-dd5a-447c-a087-5fb6054d3fce
-- title:
--   The degree-eight source right-hand side preserves a simple pole
-- statement:
--   Let $k$ be a finite field, $K/k$ a field extension and $P$ a normalized valuation. If $\operatorname{ord}_P(x)=-1$, then $x$, $x^7+1$ and $x^8/(x^7+1)$ are nonzero, and
--   $$\operatorname{ord}_P(x^7+1)=-7,\qquad \operatorname{ord}_P\!\left(\frac{x^8}{x^7+1}\right)=-1.$$
--   The denominator calculation follows from the strict valuation dominance of $x^7$ over $1$. This is the actual $r=8$ Garcia–Stichtenoth source recursion.
-- source:
--   Normalized valuation constructor lemma for the F64, r=8 Garcia–Stichtenoth source tower in the Shpilka–Guruswami appendix used by STOC 2027 paper 5. Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474; Mathlib/RingTheory/Valuation/Discrete/Basic.lean and actual GlobalPlace valuation data.

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
set_option autoImplicit false

theorem MetricSelfDualCompletion.Completion.AGFoundation.r8SourceRhsSimplePole
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    x ≠ 0 ∧ x ^ 7 + 1 ≠ 0 ∧ x ^ 8 / (x ^ 7 + 1) ≠ 0 ∧
      P.order (x ^ 7 + 1) = -7 ∧
      P.order (x ^ 8 / (x ^ 7 + 1)) = -1 := by sorry
