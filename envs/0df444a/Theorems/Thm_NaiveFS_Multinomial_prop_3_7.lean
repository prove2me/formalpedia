-- Prove2me | Theorems.Thm_NaiveFS_Multinomial_prop_3_7
-- name    : NaiveFS.Multinomial.prop_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:40.490226+00:00
-- url     : https://prove2.me/theorems/3268a1c3-98e7-468c-bbd5-6463f3a331c1
-- title:
--   Proposition 3.7, p. 11 — strong duality between (USMNB) and its dual (D), with (D) corrected
-- statement:
--   Let $f^\pm\in\mathbb R^m$ with $f^\pm_i>0$, $g=f^++f^-$, and $k<m$. Consider
--   $$\max_{x,z}\ z^\top(g\circ\log g)+x^\top(f^+\circ\log f^++f^-\circ\log f^-)+(x^\top g)\log(x^\top g)-(\mathbf 1^\top g)\log(\mathbf 1^\top g)-(x^\top f^+)\log(x^\top f^+)-(x^\top f^-)\log(x^\top f^-)$$
--   $$\text{s.t.}\quad x+z=\mathbf 1,\quad\mathbf 1^\top x\le k,\quad x\ge0,\quad z\ge0.\qquad\text{(D)}$$
--   The maximum of (D) is attained and equals the optimal value $\psi(k)$ of (USMNB).
--
--   (D) is the dual of the relaxation, and its solutions are what §3.7 rounds into feasible points of the sparse problem.
--
--   **Formalization Note** The printed (D) contains an additional term $-(x^\top g)$. It arises from dropping $\alpha(p^++p^-)=x^\top g$ in the last reduction of the proof (p. 12, setting $\alpha=x^\top g$); with it the maximum of (D) is strictly below $\psi(k)$ (numerically, e.g. $-118.30$ against $-115.92$), so the printed strong-duality claim is false. This item states the corrected (D). $z$ is eliminated as $z=\mathbf 1-x$, and $x\in\mathbb R^m$ (the page writes $\mathbb R^n$). At $x^\top f^\pm=0$, $0\log0=0$.
-- source:
--   Askari, d'Aspremont & El Ghaoui, Naive Feature Selection, arXiv:1905.09884v4, p. 11, Proposition 3.7 (D); proof pp. 11–12

import Mathlib
import Definitions.Def_NaiveFS_Multinomial_Model
import Definitions.Def_NaiveFS_Multinomial_Dual

namespace NaiveFS.Multinomial

/-- Proposition 3.7, p. 11, with (D) corrected (no `−(xᵀg)` term): strong duality between
(USMNB) and its dual (D), i.e. the maximum of (D) over `x ∈ [0,1]ᵐ`, `1ᵀx ≤ k` (with
`z = 1 − x`) exists and equals `ψ(k)`. -/
theorem prop_3_7 {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (k : ℕ) (hkm : k < m) :
    IsGreatest (Dobj fp fm '' {x | DFeasible k x}) (psi fp fm k) := by sorry

end NaiveFS.Multinomial
