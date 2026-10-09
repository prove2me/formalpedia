-- Prove2me | Theorems.Thm_LasserreFC_FinConv_theorem_3_1
-- name    : LasserreFC.FinConv.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:33:11.888977+00:00
-- url     : https://prove2.me/theorems/d8ab0eb1-f71c-48b9-bb01-1fcc09edc31a
-- title:
--   Theorem 3.1, p. 6 — CQ, strict complementarity and SOSC at a local minimizer imply the boundary hessian condition
-- statement:
--   Let $u$ be a local minimizer of (1.1), i.e. $u \in K$ and $f(x) \ge f(u)$ for all $x \in K$ near $u$. Suppose that the constraint qualification condition holds at $u$ and that there are Lagrange multipliers $\lambda, \mu$ satisfying the first order condition (1.3), complementarity (1.4), strict complementarity (1.5) and the second order sufficiency condition (1.7). Then
--
--   $$f \text{ satisfies the boundary hessian condition (Conditions 2.2–2.3) at } u.$$
--
--   The classical optimality conditions only require linear algebra at $u$, whereas the boundary hessian condition requires a local parametrization of $K$; this theorem lets Marshall's representation theorem be applied under the classical conditions.
--
--   **Formalization Note** The local-minimizer hypothesis is kept as on the page. The boundary hessian condition is the chart-based definition `IsBHC` (a $C^\infty$ parametrization of $V_{\mathbb R}(h)$ near $u$ whose first $r$ coordinates are $g_{\nu_1}, \dots, g_{\nu_r}$).
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 6, Theorem 3.1

import Mathlib
import Definitions.Def_LasserreFC_FinConv_Setting
import Definitions.Def_LasserreFC_FinConv_BHC

namespace LasserreFC.FinConv

open MvPolynomial

/-- Theorem 3.1, p. 6: at a local minimizer `u` of (1.1) where CQC, SCC and SOSC hold, `f` satisfies
the boundary hessian condition. -/
theorem theorem_3_1 {n m1 m2 : ℕ} (P : POP n m1 m2) (u : Fin n → ℝ) (hu : u ∈ P.K)
    (hloc : IsLocalMinOn (fun x => eval x P.f) P.K u) (hopt : OptCond P u) :
    IsBHC P u := by sorry

end LasserreFC.FinConv
