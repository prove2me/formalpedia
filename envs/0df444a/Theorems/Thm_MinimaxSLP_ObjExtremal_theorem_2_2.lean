-- Prove2me | Theorems.Thm_MinimaxSLP_ObjExtremal_theorem_2_2
-- name    : MinimaxSLP.ObjExtremal.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:55.255997+00:00
-- url     : https://prove2.me/theorems/b7d75804-6446-474c-8e78-807009a7b520
-- title:
--   Theorem 2.2, p. 585 — distributions in $\mathcal P$ asymptotically achieve $Z(x)=Z_D(x)=Z_{DD}(x)$
-- statement:
--   Consider the two-stage minimax stochastic linear program with random objective $\tilde q$, first-stage region $X$, recourse set $X(x)=\{w\ge0 : Ww=h-Tx\}$, second-stage cost $\mathcal Q(q,x)=\min_{w\in X(x)}q'w$, disutility $\mathbb U(t)=\max_k(\alpha_kt+\beta_k)$ with $\alpha_k\ge0$, and moment class $\mathcal P$ of distributions on $\mathbb R^d$ with mean $\mu$ and second-moment matrix $Q$. Assume $X(x)\neq\emptyset$, Assumption 3 ($\{p : W'p\le q\}\neq\emptyset$ for every $q\in\mathbb R^d$) and Assumption 4 ($Q$ symmetric, $Q-\mu\mu'\succ0$).
--
--   **Theorem 2.2.** For an arbitrary $x\in X$:
--
--   1. there is a sequence $(P_j)_{j\ge1}$ of distributions in $\mathcal P$ with
--   $$
--   \lim_{j\to\infty}\mathbb E_{P_j}\big[\mathbb U(\mathcal Q(\tilde q,x))\big]=Z(x);
--   $$
--   2. the three optimal values are finite and genuine: $Z(x)$ is the supremum of the values $\mathbb E_P[\mathbb U(\mathcal Q(\tilde q,x))]$, $P\in\mathcal P$; $Z_D(x)$ is the infimum of the objective of the dual (6) over its (nonempty) feasible set; and $Z_{DD}(x)$ is the supremum of the objective of the semidefinite program (9) over its (nonempty) feasible set;
--   3. they coincide:
--   $$
--   Z(x)=Z_D(x)=Z_{DD}(x).
--   $$
--
--   The theorem identifies the worst-case expected disutility with the value of a semidefinite program whose optimal solution encodes the conditional moments of near-extremal distributions; the paper builds these distributions explicitly as mixtures of point masses and rare Gaussian perturbations.
--
--   **Formalization Note** Part 1 on its own is a property of every finite supremum, so the content of the theorem is in parts 2 and 3. Distributions are probability measures with finite second moments rather than densities. Assumptions 2 and 3 of the paper contradict each other as printed when $r\ge1$; this statement uses what §2's proofs use: Assumption 3 for all $q$ and nonempty recourse sets $X(x)$ in place of complete recourse. Assumption 1 (boundedness of $X$) is not used and is omitted. The printed max of (9) is attained (a separate milestone); here $Z_{DD}(x)$ is its supremum.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 585, Theorem 2.2 (proof pp. 586–587)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjExtremal_Model

open MeasureTheory Matrix Filter Topology

namespace MinimaxSLP.ObjExtremal

/-- Theorem 2.2 (p. 585): for every `x ∈ MinimaxSLP.ObjSDP.X` there is a sequence of distributions in `𝒫` whose
expected disutilities converge to the optimal value `Z(x) = Z_D(x) = Z_DD(x)`. All three optimal
values are genuine (least upper bound of the primal values, greatest lower bound of the values of
(6), least upper bound of the values of (9)) and coincide. -/
theorem theorem_2_2 {m₁ n r d K : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hx : x ∈ MinimaxSLP.ObjSDP.X A b) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty) :
    (∃ P : ℕ → Measure (Fin d → ℝ), (∀ j, P j ∈ MinimaxSLP.ObjSDP.momentClass μ Q) ∧
      Tendsto (fun j => ∫ q, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.ObjSDP.Qval W T h q x) ∂(P j)) atTop
        (𝓝 (MinimaxSLP.ObjSDP.Zx W T h α β μ Q x))) ∧
    IsLUB (MinimaxSLP.ObjSDP.primalValues W T h α β μ Q x) (MinimaxSLP.ObjSDP.Zx W T h α β μ Q x) ∧
    IsGLB (MinimaxSLP.ObjSDP.dualValues6 W T h α β μ Q x) (MinimaxSLP.ObjSDP.ZD W T h α β μ Q x) ∧
    IsLUB (dualValues9 W T h α β μ Q x) (ZDD W T h α β μ Q x) ∧
    MinimaxSLP.ObjSDP.Zx W T h α β μ Q x = MinimaxSLP.ObjSDP.ZD W T h α β μ Q x ∧
    MinimaxSLP.ObjSDP.ZD W T h α β μ Q x = ZDD W T h α β μ Q x := by sorry

end MinimaxSLP.ObjExtremal
