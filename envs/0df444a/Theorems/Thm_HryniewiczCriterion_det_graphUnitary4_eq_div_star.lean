-- Prove2me | Theorems.Thm_HryniewiczCriterion_det_graphUnitary4_eq_div_star
-- name    : HryniewiczCriterion.det_graphUnitary4_eq_div_star
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T20:03:12.429509+00:00
-- url     : https://prove2.me/theorems/96ffb644-9a5b-4ffe-b309-ce73a993a40a
-- title:
--   Determinant of the graph unitary $W(\Gamma_g)\,W(\Delta)^{-1}$ on $\mathbb{R}^4$
-- statement:
--   Let $g$ be a real $4\times4$ matrix and let $\Gamma_g=\{(z,gz)\}\subset\mathbb{R}^4\oplus\mathbb{R}^4$ be its graph. Let $A_g=\texttt{graphBasis4}\ g$ be the complex $4\times4$ matrix whose columns encode a basis of $\Gamma_g$, and set $\delta(g)=\det A_g$. If $\delta(g)\neq0$, then the unitary $W(\Gamma_g)\,W(\Delta)^{-1}$, built from the Souriau map $W(L)=UU^T$, satisfies
--   $$\det\bigl(W(\Gamma_g)\,W(\Delta)^{-1}\bigr)=\frac{\delta(g)}{\overline{\delta(g)}} .$$
--
--   So the determinant angle of the graph unitary is twice the argument of the polynomial $\delta(g)$. This reduces determinant-angle computations for paths in $Sp(4)$ to tracking the argument of a single complex number.
--
--   **Formalization note.** $\delta(g)=4\det_{\mathbb{C}}A$, where $gz=Az+C\bar z$ in the coordinates $z_k=q_k+ip_k$.
-- source:
--   Standard computation for the Souriau map $W(L)=UU^T$; used for the determinant-angle argument in the index estimate of Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, Theorem 3.4, pp. 219–222.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.det_graphUnitary4_eq_div_star (g : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : (graphBasis4 g).det ≠ 0) :
    (graphUnitary4 g).det = (graphBasis4 g).det / star (graphBasis4 g).det := by sorry
