-- Prove2me | Theorems.Thm_MinimaxSLP_ObjExtremal_dual9_attained
-- name    : MinimaxSLP.ObjExtremal.dual9_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:09.536978+00:00
-- url     : https://prove2.me/theorems/ea3e3c4a-b48b-4744-80d6-b532ef4d96ab
-- title:
--   Proof of Theorem 2.2, p. 586 — the semidefinite program (9) has an optimal solution
-- statement:
--   Let $x\in X$, assume $X(x)\neq\emptyset$, Assumption 3 ($\{p : W'p\le q\}\neq\emptyset$ for all $q\in\mathbb R^d$), $\alpha_k\ge0$ for all $k$, and Assumption 4 ($Q$ symmetric, $Q-\mu\mu'\succ0$). Then the maximization problem (9),
--   $$
--   \max\ \sum_{k=1}^K (h-Tx)'p_k+\beta_k v_{k0}\quad\text{s.t.}\quad \sum_{k=1}^K\begin{pmatrix}V_k & v_k\\ v_k' & v_{k0}\end{pmatrix}=\begin{pmatrix}Q&\mu\\ \mu'&1\end{pmatrix},\ \ \begin{pmatrix}V_k & v_k\\ v_k' & v_{k0}\end{pmatrix}\succeq 0,\ \ W'p_k\le\alpha_k v_k,
--   $$
--   has an optimal solution: there is a feasible $(V_k,v_k,v_{k0},p_k)_{k=1}^K$ whose objective value is at least that of every feasible point.
--
--   The proof of Theorem 2.2 starts from such an optimal solution; the paper takes its existence for granted.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 586, proof of Theorem 2.2 (first sentence)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjExtremal_Model

open MeasureTheory Matrix Filter Topology

namespace MinimaxSLP.ObjExtremal

/-- Proof of Theorem 2.2 (p. 586): the dual problem (9) has an optimal solution
`(V_k, v_k, v_k0, p_k)_{k}`, i.e. a feasible point whose objective value is the largest. -/
theorem dual9_attained {m₁ n r d K : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hx : x ∈ MinimaxSLP.ObjSDP.X A b) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty) :
    ∃ s ∈ feasible9 W α μ Q, ∀ s' ∈ feasible9 W α μ Q, obj9 T h β x s' ≤ obj9 T h β x s := by sorry

end MinimaxSLP.ObjExtremal
