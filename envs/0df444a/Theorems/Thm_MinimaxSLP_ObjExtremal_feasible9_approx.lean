-- Prove2me | Theorems.Thm_MinimaxSLP_ObjExtremal_feasible9_approx
-- name    : MinimaxSLP.ObjExtremal.feasible9_approx
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-05T22:38:35.911886+00:00
-- url     : https://prove2.me/theorems/5a56bb24-253d-4ce2-8c76-32b841108a6b
-- title:
--   Proof of Theorem 2.2, pp. 586–587 — distributions in $\mathcal P$ approach the value of any feasible point of (9)
-- statement:
--   Consider the two-stage minimax stochastic linear program with random objective $\tilde q$ of §2: recourse set $X(x)=\{w\ge 0 : Ww=h-Tx\}$, second-stage value $\mathcal Q(q,x)=\min_{w\in X(x)} q'w$, piecewise-linear disutility $\mathbb U(t)=\max_k(\alpha_k t+\beta_k)$ with $\alpha_k\ge 0$, and moment class $\mathcal P$ of probability measures on $\mathbb R^d$ (with finite second moments) having mean $\mu$ and second-moment matrix $Q$. Assume $X(x)\neq\emptyset$ and Assumption 3: $\{p : W'p\le q\}\neq\emptyset$ for every $q\in\mathbb R^d$.
--
--   Let $(V_k,v_k,v_{k0},p_k)_{k=1,\dots,K}$ be any feasible solution of the semidefinite program (9), i.e.
--   $$
--   \sum_{k}\begin{pmatrix}V_k & v_k\\ v_k' & v_{k0}\end{pmatrix}=\begin{pmatrix}Q & \mu\\ \mu' & 1\end{pmatrix},\qquad \begin{pmatrix}V_k & v_k\\ v_k' & v_{k0}\end{pmatrix}\succeq 0,\qquad W'p_k\le \alpha_k v_k .
--   $$
--   Then for every $\delta>0$ there is a distribution $P\in\mathcal P$ such that $\mathbb U(\mathcal Q(\cdot,x))$ is $P$-integrable and
--   $$
--   \mathbb E_P\big[\mathbb U(\mathcal Q(\tilde q,x))\big]\ \ge\ \sum_{k}\big((h-Tx)'p_k+\beta_k v_{k0}\big)-\delta .
--   $$
--
--   This is the construction step of the proof of Theorem 2.2: the paper builds, from an optimal solution of (9), distributions that put mass $v_{k0}$ near the conditional mean $v_k/v_{k0}$ with a rare large perturbation $r_k/\sqrt{\epsilon}$ carrying the remaining second moment, and uses homogeneity and superadditivity of $\mathcal Q(\cdot,x)$ together with $\alpha_k\mathcal Q(v_k,x)\ge (h-Tx)'p_k$ to bound the expected disutility from below by the objective of (9) up to an error that vanishes as $\epsilon\to 0$. It gives $Z(x)\ge Z_{DD}(x)$. The statement here is for an arbitrary feasible point of (9) (no optimality or attainment is assumed).
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, proof of Theorem 2.2, pp. 586–587

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjExtremal_Model

open MeasureTheory Matrix Filter Topology

namespace MinimaxSLP.ObjExtremal

/-- Proof of Theorem 2.2 (pp. 586–587), the construction step: every feasible solution
`(V_k, v_k, v_k0, p_k)_k` of (9) is approached from below by distributions of the moment class
`𝒫`: for every `δ > 0` there is `P ∈ 𝒫` with `𝕌(𝒬(·, x))` integrable and
`E_P[𝕌(𝒬(q̃, x))] ≥ Σ_k ((h − T x)′p_k + β_k v_k0) − δ`. (The paper applies it to an optimal
solution of (9); it yields `Z(x) ≥ Z_DD(x)`.) -/
theorem feasible9_approx {n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty)
    (s : (Fin K → Matrix (Fin d) (Fin d) ℝ) × (Fin K → Fin d → ℝ) × (Fin K → ℝ) ×
      (Fin K → Fin r → ℝ))
    (hs : s ∈ feasible9 W α μ Q) (δ : ℝ) (hδ : 0 < δ) :
    ∃ P ∈ MinimaxSLP.ObjSDP.momentClass μ Q,
      Integrable (fun q => MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.ObjSDP.Qval W T h q x)) P ∧
      obj9 T h β x s - δ ≤
        ∫ q, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.ObjSDP.Qval W T h q x) ∂P := by sorry

end MinimaxSLP.ObjExtremal
