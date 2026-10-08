-- Prove2me | Theorems.Thm_MinimaxSLP_ObjExtremal_zero_weight_reduction
-- name    : MinimaxSLP.ObjExtremal.zero_weight_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:41.55732+00:00
-- url     : https://prove2.me/theorems/419b0765-627f-4acb-987f-4db90e3e7486
-- title:
--   Proof of Theorem 2.2, p. 587 — an optimal solution of (9) whose blocks have $v_{k0}>0$ or vanish
-- statement:
--   Let $x\in X$, assume $X(x)\neq\emptyset$, Assumption 3, $\alpha_k\ge0$ for all $k$ and Assumption 4. Let $(V_k,v_k,v_{k0},p_k)_{k=1}^K$ be an optimal solution of (9). Then there is another feasible point $(V'_k,v'_k,v'_{k0},p'_k)_{k=1}^K$ of (9) with the same objective value (hence also optimal) and the same weights, $v'_{k0}=v_{k0}$ for all $k$, such that for every $k$ either
--   $$
--   v'_{k0}>0\qquad\text{or}\qquad V'_k=0,\ v'_k=0,\ v'_{k0}=0,\ p'_k=0 .
--   $$
--   In particular, writing $L=\{k : v_{k0}=0\}$ (the same set for both solutions),
--   $$
--   \sum_{k\notin L}\begin{pmatrix}V'_k & v'_k\\ v'_k{}' & v'_{k0}\end{pmatrix}=\begin{pmatrix}Q&\mu\\ \mu'&1\end{pmatrix}.
--   $$
--
--   This reduces the construction of the extremal distributions of Theorem 2.2 to the case where every block that is used has positive weight $v_{k0}$.
--
--   **Formalization Note** The paper's construction sets $V_k:=0$ for $k\in L$ and leaves $p_k$ unchanged, noting $(h-Tx)'p_k+v_{k0}\beta_k=0$ for $k\in L$. Here $p'_k=0$ is required for the zero blocks; it gives the same objective value, by that identity.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 587, proof of Theorem 2.2 (the case v_k0 = 0 for k ∈ L)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjExtremal_Model

open MeasureTheory Matrix Filter Topology

namespace MinimaxSLP.ObjExtremal

/-- Proof of Theorem 2.2 (p. 587): from an optimal solution of (9) one obtains an optimal
solution with the same objective value in which every block either has `v_k0 > 0` or is entirely
zero (`V_k = 0`, `v_k = 0`, `v_k0 = 0`, `p_k = 0`), and the weights `v_k0` are those of the
given solution; so with `L = {k : v_k0 = 0}` the blocks with `k ∉ L` alone sum to
`( Q μ ; μ′ 1 )`. -/
theorem zero_weight_reduction {m₁ n r d K : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hx : x ∈ MinimaxSLP.ObjSDP.X A b) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty)
    (s : (Fin K → Matrix (Fin d) (Fin d) ℝ) × (Fin K → Fin d → ℝ) × (Fin K → ℝ) ×
      (Fin K → Fin r → ℝ))
    (hs : s ∈ feasible9 W α μ Q)
    (hopt : ∀ s' ∈ feasible9 W α μ Q, obj9 T h β x s' ≤ obj9 T h β x s) :
    ∃ s' ∈ feasible9 W α μ Q, obj9 T h β x s' = obj9 T h β x s ∧
      (∀ k, s'.2.2.1 k = s.2.2.1 k) ∧
      ∀ k, 0 < s'.2.2.1 k ∨
        (s'.1 k = 0 ∧ s'.2.1 k = 0 ∧ s'.2.2.1 k = 0 ∧ s'.2.2.2 k = 0) := by sorry

end MinimaxSLP.ObjExtremal
