-- Prove2me | Theorems.Thm_LasserreFC_Generic_lemma_4_6
-- name    : LasserreFC.Generic.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:26.430093+00:00
-- url     : https://prove2.me/theorems/2858d3c8-4c8e-4ceb-85e8-d3b8a64468c6
-- title:
--   Lemma 4.6, p. 15 — at a local minimizer with G(u) of full rank, SOSC holds iff det H(u) ≠ 0
-- statement:
--   Let $u$ be a local minimizer of (1.1) and let $\lambda,\mu$ satisfy (1.3)–(1.4), including $\mu_j\ge0$. Let
--   $$H(u)=\begin{bmatrix}\nabla^2_xL(u)&G(u)^T\\ G(u)&0\end{bmatrix},$$
--   where $L(x)=f(x)-\sum_i\lambda_ih_i(x)-\sum_{j\in J(u)}\mu_jg_j(x)$ and $G(u)$ has rows $\nabla h_1(u)^T,\dots,\nabla h_{m_1}(u)^T,\nabla g_j(u)^T$ ($j\in J(u)$). If $G(u)$ has full row rank, then the second order sufficiency condition (1.7),
--   $$v^T\nabla_x^2L(u)v>0\quad\text{for all }0\neq v\in G(u)^\perp,$$
--   holds if and only if $\det H(u)\neq0$.
--
--   This lemma converts the nonsingularity of $H(u)$, obtained from Condition 4.3 (d), into the second order sufficiency condition.
--
--   **Formalization Note** "$G(u)$ has full rank" is stated as the constraint qualification condition, i.e. linear independence of the rows of $G(u)$. The determinant does not depend on the order of the rows up to sign.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 15, Lemma 4.6 (L, G, H from p. 14)

import Mathlib
import Definitions.Def_LasserreFC_Generic_Setting

namespace LasserreFC.Generic

open MvPolynomial

/-- Lemma 4.6, p. 15. Let `u` be a local minimizer of (1.1) and `λ, μ` satisfy (1.3)–(1.4)
(including `μⱼ ≥ 0`). If `G(u)` has full rank (its rows `∇h₁(u), …, ∇h_{m₁}(u), ∇gⱼ(u)`,
`j ∈ J(u)`, are linearly independent, i.e. CQC holds at `u`), then the second order sufficiency
condition (1.7) holds at `u` if and only if `det H(u) ≠ 0`. -/
theorem lemma_4_6 {n m1 m2 : ℕ} (P : POP n m1 m2) (u : Fin n → ℝ) (hu : u ∈ P.K)
    (hmin : IsLocalMinOn (fun x => eval x P.f) P.K u) (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ)
    (hkkt : IsKKTMult P u lam mu) (hG : CQC P u) :
    SOSC P u lam mu ↔ (Hmat P u lam mu).det ≠ 0 := by sorry

end LasserreFC.Generic
