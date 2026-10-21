-- Prove2me | Theorems.Thm_NashPoly_Generic_ne_satisfies_3_6
-- name    : NashPoly.Generic.ne_satisfies_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:59.60299+00:00
-- url     : https://prove2.me/theorems/2301f07e-82fe-49b5-8b6a-cb73b0ddc42a
-- title:
--   §3.1, (3.6), p. 8 — with polynomial multiplier expressions, every Nash equilibrium satisfies (3.6)
-- statement:
--   Let a NEPP be given by objectives $f_i\in\mathbb R[x]$, constraints $g_{i,j}\in\mathbb R[x_i]$ and equality labels $E_i$ (with $I_i=[m_i]\setminus E_i$). Suppose that for every player $i$ there is a matrix polynomial $H_i(x_i)$ with
--   $$H_i(x_i)\,G_i(x_i)=I_{m_i}$$
--   as an identity of polynomial matrices, where $G_i$ is the matrix (3.1), and let $\lambda_{i,j}(x)=(H_i(x_i)\hat f_i(x))_j$. Then every Nash equilibrium $x$ satisfies the polynomial system (3.6):
--   $$\nabla_{x_i}f_i(x)-\sum_{j=1}^{m_i}\lambda_{i,j}(x)\nabla_{x_i}g_{i,j}(x_i)=0\ (i\in[N]),\qquad g_{i,j}(x_i)=0\ (j\in E_i),$$
--   $$\lambda_{i,j}(x)g_{i,j}(x_i)=0,\quad g_{i,j}(x_i)\ge0,\quad\lambda_{i,j}(x)\ge0\quad(j\in I_i).$$
--   That is, the set $G^*$ of Nash equilibria is contained in the feasible set $G$ of (3.7).
--
--   This is the reason Algorithm 3.1 may search for equilibria inside $G$: no equilibrium is lost by imposing the KKT conditions with polynomial multipliers.
--
--   **Formalization Note** The hypothesis $H_iG_i=I$ is the paper's (3.2); it implies that $g_i$ is nonsingular. Nash equilibria are global: each block minimizes $f_i(\cdot,x_{-i})$ over all of $X_i$.
-- source:
--   Nie & Tang, Nash Equilibrium Problems of Polynomials, arXiv:2006.09490v2, p. 8, §3.1, (3.2), (3.3), (3.6)

import Mathlib
import Definitions.Def_NashPoly_Generic_MultiplierExpr

namespace NashPoly.Generic

open MvPolynomial Matrix

/-- §3.1, (3.6), p. 8: if every constraining tuple admits a matrix polynomial `H_i(x_i)` with
`H_i(x_i) G_i(x_i) = I_{m_i}` (identity of polynomial matrices, (3.2)), then every Nash
equilibrium satisfies the polynomial system (3.6) with `λ_{i,j}(x) = (H_i(x_i) f̂_i(x))_j`. -/
theorem ne_satisfies_3_6 {N : ℕ} {n m : Fin N → ℕ} (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (hH : ∀ i, H i * Gmat (P.g i) = 1) :
    P.NESet ⊆ P.GSet H := by sorry

end NashPoly.Generic
