-- Prove2me | Theorems.Thm_MinimaxSLP_ObjExtremal_lemma_2_1
-- name    : MinimaxSLP.ObjExtremal.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:06.500181+00:00
-- url     : https://prove2.me/theorems/0fa8e420-01aa-4b3e-b7d3-29d7a3b42efa
-- title:
--   Lemma 2.1, p. 585 — for x ∈ X, $Z_{DD}(x) \ge Z(x)$: every $P\in\mathcal P$ yields a feasible point of (9) with value $\mathbb E_P[\mathbb U(\mathcal Q)]$
-- statement:
--   Let $x\in X$ and assume that $X(x)\neq\emptyset$, that $\{p\in\mathbb R^r : W'p\le q\}\neq\emptyset$ for every $q\in\mathbb R^d$ (Assumption 3), that $\alpha_k\ge 0$ for all $k$, and that $Q$ is symmetric with $Q-\mu\mu'\succ 0$ (Assumption 4). Then:
--
--   1. for every $P\in\mathcal P$ the function $q\mapsto\mathbb U(\mathcal Q(q,x))$ is $P$-integrable, and there is a feasible point $(V_k,v_k,v_{k0},p_k)_{k=1}^K$ of (9) whose objective value equals the expectation:
--   $$
--   \mathbb E_P\big[\mathbb U(\mathcal Q(\tilde q,x))\big]=\sum_{k=1}^K (h-Tx)'p_k+\beta_k v_{k0};
--   $$
--   2. consequently
--   $$
--   Z(x)=\sup_{P\in\mathcal P}\mathbb E_P\big[\mathbb U(\mathcal Q(\tilde q,x))\big]\le Z_{DD}(x).
--   $$
--
--   The feasible point of part 1 consists of the scaled conditional moments of $\tilde q$ and of a dual-optimal solution of the second-stage problem on the event that the $k$th piece of $\mathbb U$ attains the maximum (ties broken arbitrarily). This upper bound is one half of the identity $Z(x)=Z_{DD}(x)$ of Theorem 2.2.
--
--   **Formalization Note** Part 1 is the form in which the paper's proof establishes the lemma; part 2 is the printed statement. Integrability is stated explicitly because the Bochner integral of a non-integrable function is $0$ in Lean.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 585, Lemma 2.1 and its proof

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjExtremal_Model

open MeasureTheory Matrix Filter Topology

namespace MinimaxSLP.ObjExtremal

/-- Lemma 2.1 (p. 585): for every `x ∈ MinimaxSLP.ObjSDP.X`, `Z_DD(x) ≥ Z(x)`. In the form the proof gives it:
every `P ∈ 𝒫` has an integrable `𝕌(𝒬(·, x))` and a feasible point of (9) (the scaled
conditional moments) whose objective value equals `E_P[𝕌(𝒬(q̃, x))]`; hence `Z(x) ≤ Z_DD(x)`. -/
theorem lemma_2_1 {m₁ n r d K : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hx : x ∈ MinimaxSLP.ObjSDP.X A b) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty) :
    (∀ P ∈ MinimaxSLP.ObjSDP.momentClass μ Q,
      Integrable (fun q => MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.ObjSDP.Qval W T h q x)) P ∧
      ∃ s ∈ feasible9 W α μ Q, ∫ q, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.ObjSDP.Qval W T h q x) ∂P = obj9 T h β x s) ∧
    MinimaxSLP.ObjSDP.Zx W T h α β μ Q x ≤ ZDD W T h α β μ Q x := by sorry

end MinimaxSLP.ObjExtremal
