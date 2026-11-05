-- Prove2me | Theorems.Thm_LasserreFC_Generic_kkt_first_order
-- name    : LasserreFC.Generic.kkt_first_order
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T12:44:14.839222+00:00
-- url     : https://prove2.me/theorems/1de4c0af-e0ac-4550-aa48-6fec0fc3de45
-- title:
--   p. 2, (1.3)–(1.4) — under CQC a local minimizer of (1.1) admits KKT multipliers
-- statement:
--   Consider problem (1.1),
--   $$
--   \min_{x\in\mathbb R^n} f(x)\quad\text{s.t.}\quad h_i(x)=0\ (i\in[m_1]),\qquad g_j(x)\ge0\ (j\in[m_2]),
--   $$
--   with $f,h_i,g_j\in\mathbb R[x]$ and feasible set $K$. Let $u\in K$ be a local minimizer of $f$ on $K$, let $J(u)=\{j: g_j(u)=0\}$ be the active set, and assume the constraint qualification condition (CQC): the gradients $\nabla h_1(u),\dots,\nabla h_{m_1}(u)$, $\nabla g_j(u)$ $(j\in J(u))$ are linearly independent.
--
--   Then there exist Lagrange multipliers $\lambda_1,\dots,\lambda_{m_1}$ and $\mu_1,\dots,\mu_{m_2}$ such that
--   $$
--   \nabla f(u)=\sum_{i=1}^{m_1}\lambda_i\nabla h_i(u)+\sum_{j=1}^{m_2}\mu_j\nabla g_j(u)\qquad(1.3)
--   $$
--   $$
--   \mu_1g_1(u)=\cdots=\mu_{m_2}g_{m_2}(u)=0,\qquad \mu_1\ge0,\ \dots,\ \mu_{m_2}\ge0.\qquad(1.4)
--   $$
--
--   These are the classical Karush–Kuhn–Tucker first order optimality and complementarity conditions, recalled on p. 2 of the paper from Bertsekas, *Nonlinear Programming*, §3.3. They are used in the proof of Proposition 4.5 to produce the multipliers to which Proposition 4.4 and Lemma 4.6 are applied.
--
--   **Formalization Note** Gradients are formal partial derivatives evaluated at $u$; local minimality is `IsLocalMinOn` relative to $K$.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 2, paragraph preceding (1.3) and equations (1.3)–(1.4) (citing D. Bertsekas, Nonlinear Programming, 2nd ed., §3.3); used in the proof of Proposition 4.5, p. 15

import Mathlib
import Definitions.Def_LasserreFC_Generic_Setting

namespace LasserreFC.Generic

open MvPolynomial

/-- p. 2 (first order optimality conditions, cf. Bertsekas [1, §3.3]). Let `u` be a local
minimizer of (1.1). If the constraint qualification condition holds at `u`, then there exist
Lagrange multipliers `λ₁, …, λ_{m₁}` and `μ₁, …, μ_{m₂}` satisfying (1.3)–(1.4):
`∇f(u) = Σᵢ λᵢ ∇hᵢ(u) + Σⱼ μⱼ ∇gⱼ(u)`, `μⱼ gⱼ(u) = 0` and `μⱼ ≥ 0` for all `j`. -/
theorem kkt_first_order {n m1 m2 : ℕ} (P : POP n m1 m2) (u : Fin n → ℝ) (hu : u ∈ P.K)
    (hmin : IsLocalMinOn (fun x => eval x P.f) P.K u) (hcq : CQC P u) :
    ∃ (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ), IsKKTMult P u lam mu := by sorry

end LasserreFC.Generic
