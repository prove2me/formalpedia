-- Prove2me | Theorems.Thm_LasserreFC_Generic_sonc_1_6
-- name    : LasserreFC.Generic.sonc_1_6
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T12:44:09.192134+00:00
-- url     : https://prove2.me/theorems/f68a9c75-f72c-46ab-9a69-5fe5f957031b
-- title:
--   p. 3, (1.6) — under CQC the second order necessity condition holds at a local minimizer
-- statement:
--   Consider problem (1.1),
--   $$
--   \min_{x\in\mathbb R^n} f(x)\quad\text{s.t.}\quad h_i(x)=0\ (i\in[m_1]),\qquad g_j(x)\ge0\ (j\in[m_2]),
--   $$
--   with $f,h_i,g_j\in\mathbb R[x]$ and feasible set $K$. Let $u\in K$ be a local minimizer of $f$ on $K$, let $J(u)=\{j: g_j(u)=0\}$ be the active set, and assume the constraint qualification condition (CQC): the gradients $\nabla h_1(u),\dots,\nabla h_{m_1}(u)$, $\nabla g_j(u)$ $(j\in J(u))$ are linearly independent. Let $\lambda,\mu$ satisfy (1.3)–(1.4) and let
--   $$
--   L(x)=f(x)-\sum_{i=1}^{m_1}\lambda_ih_i(x)-\sum_{j\in J(u)}\mu_jg_j(x)
--   $$
--   be the Lagrange function of p. 3. Then the second order necessity condition (1.6) holds:
--   $$
--   v^T\nabla^2_xL(u)\,v\ \ge\ 0\qquad\text{for all } v\in G(u)^\perp,
--   $$
--   where $G(u)^\perp$ is the set of $v\in\mathbb R^n$ with $\nabla h_i(u)^Tv=0$ for all $i$ and $\nabla g_j(u)^Tv=0$ for all $j\in J(u)$.
--
--   This is the classical second order necessary condition for constrained minima (Bertsekas, *Nonlinear Programming*, §3.3), stated on p. 3 of the paper. It is used in the proof of Lemma 4.6 to show that $\det H(u)\ne0$ forces the second order sufficiency condition (1.7).
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 3, (1.6) (citing D. Bertsekas, Nonlinear Programming, 2nd ed., §3.3); used in the proof of Lemma 4.6, pp. 15–16

import Mathlib
import Definitions.Def_LasserreFC_Generic_Setting

namespace LasserreFC.Generic

open MvPolynomial Matrix

/-- p. 3, (1.6) (second order necessity condition, cf. Bertsekas [1, §3.3]). Let `u` be a local
minimizer of (1.1) and `λ, μ` satisfy (1.3)–(1.4). If the constraint qualification condition
holds at `u`, then `vᵀ ∇²L(u) v ≥ 0` for every `v ∈ G(u)^⊥`, i.e. every `v` orthogonal to
`∇hᵢ(u)` for all `i` and to `∇gⱼ(u)` for all active `j`, where
`L(x) = f(x) − Σᵢ λᵢ hᵢ(x) − Σ_{j ∈ J(u)} μⱼ gⱼ(x)`. -/
theorem sonc_1_6 {n m1 m2 : ℕ} (P : POP n m1 m2) (u : Fin n → ℝ) (hu : u ∈ P.K)
    (hmin : IsLocalMinOn (fun x => eval x P.f) P.K u) (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ)
    (hkkt : IsKKTMult P u lam mu) (hcq : CQC P u) :
    ∀ v : Fin n → ℝ, (∀ i, grad (P.h i) u ⬝ᵥ v = 0) →
      (∀ j, eval u (P.g j) = 0 → grad (P.g j) u ⬝ᵥ v = 0) →
      0 ≤ v ⬝ᵥ (hess (lagr P u lam mu) u *ᵥ v) := by sorry

end LasserreFC.Generic
