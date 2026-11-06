-- Prove2me | Theorems.Thm_MinimaxSLP_ObjExtremal_dual6_le_dual9_upper
-- name    : MinimaxSLP.ObjExtremal.dual6_le_dual9_upper
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-05T23:02:02.112268+00:00
-- url     : https://prove2.me/theorems/780f1187-56f3-4413-8aa9-c28f2fe135ee
-- title:
--   §2.2, pp. 584–585 — conic duality: $Z_D(x)\le Z_{DD}(x)$ under Assumption 4
-- statement:
--   Consider the two-stage minimax stochastic linear program with random objective of §2: recourse set $X(x)=\{w\ge0: Ww=h-Tx\}$, second-stage value $\mathcal Q(q,x)=\min_{w\in X(x)}q'w$, disutility $\mathbb U(t)=\max_k(\alpha_kt+\beta_k)$ with $\alpha_k\ge0$, mean $\mu$ and second-moment matrix $Q$ (symmetric). Assume $X(x)\neq\emptyset$, Assumption 3 ($\{p: W'p\le q\}\ne\emptyset$ for all $q$) and Assumption 4 ($Q-\mu\mu'\succ0$).
--
--   The dual (6) of the moment problem is
--   $$
--   Z_D(x)=\inf\Big\{Q\cdot Y+\mu'y+y_0 \;:\; q'Yq+q'y+y_0\ \ge\ \mathbb U(\mathcal Q(q,x))\ \ \forall q\in\mathbb R^d\Big\},
--   $$
--   and the semidefinite program (9) is
--   $$
--   Z_{DD}(x)=\sup\Big\{\sum_k\big((h-Tx)'p_k+\beta_kv_{k0}\big) : \sum_k\begin{pmatrix}V_k&v_k\\ v_k'&v_{k0}\end{pmatrix}=\begin{pmatrix}Q&\mu\\ \mu'&1\end{pmatrix},\ \begin{pmatrix}V_k&v_k\\ v_k'&v_{k0}\end{pmatrix}\succeq0,\ W'p_k\le\alpha_kv_k\Big\}.
--   $$
--
--   **Statement.** If $u$ is an upper bound for the objective values of (9), then for every $\varepsilon>0$ there is a feasible point $(Y,y,y_0)$ of (6), with $Y$ symmetric, such that
--   $$
--   Q\cdot Y+\mu'y+y_0\ \le\ u+\varepsilon .
--   $$
--   In particular $Z_D(x)\le Z_{DD}(x)$.
--
--   This is the conic-duality half of the identity $Z_D(x)=Z_{DD}(x)$ in Theorem 2.2. Program (9) is the semidefinite dual of (8), whose value is $Z_D(x)$, and Assumption 4 makes $\begin{pmatrix}Q&\mu\\ \mu'&1\end{pmatrix}$ positive definite. That is a Slater point for (9), so there is no duality gap. Together with weak duality and the extremal-distribution construction it gives $Z(x)=Z_D(x)=Z_{DD}(x)$.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, §2.2 pp. 584–585 (the SDP (9) as the dual of (8)) and Theorem 2.2 (Z_D(x) = Z_DD(x))

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjExtremal_Model

open MeasureTheory Matrix Filter Topology

namespace MinimaxSLP.ObjExtremal

/-- §2.2 (pp. 583–585): conic duality between the dual (6) of the moment problem and the
semidefinite program (9). Under Assumption 4 (`Q − μμ′ ≻ 0`, the Slater condition for (9)), every
upper bound `u` of the objective values of (9) is, up to any `ε > 0`, the objective value of a
feasible point of (6); in particular `Z_D(x) ≤ Z_DD(x)`. -/
theorem dual6_le_dual9_upper {n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty)
    (u : ℝ) (hu : u ∈ upperBounds (dualValues9 W T h α β μ Q x)) (ε : ℝ) (hε : 0 < ε) :
    ∃ s ∈ MinimaxSLP.ObjSDP.dualFeasible6 W T h α β x,
      MinimaxSLP.ObjSDP.frob Q s.1 + μ ⬝ᵥ s.2.1 + s.2.2 ≤ u + ε := by sorry

end MinimaxSLP.ObjExtremal
