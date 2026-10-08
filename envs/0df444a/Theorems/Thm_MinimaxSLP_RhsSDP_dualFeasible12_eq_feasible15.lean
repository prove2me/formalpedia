-- Prove2me | Theorems.Thm_MinimaxSLP_RhsSDP_dualFeasible12_eq_feasible15
-- name    : MinimaxSLP.RhsSDP.dualFeasible12_eq_feasible15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:00.709969+00:00
-- url     : https://prove2.me/theorems/febb28e2-6fdc-487d-a232-bea2dcb6d9d3
-- title:
--   Proof of Theorem 3.2, pp. 589–590 — the feasible sets of (12) and (15) coincide, so Ẑ_D(x) is the value of (15)
-- statement:
--   Let $\alpha_k\ge 0$ for all $k$, let $W,T,q$ satisfy complete recourse (Assumption 2) and $\{p : W'p\le q\}\neq\emptyset$ (Assumption 3 at the constant $q$), and let $p_1,\dots,p_N$ be the extreme points of $\{p : W'p\le q\}$ (Assumption 5). For every $x\in\mathbb R^n$, a triple $(Y,y,y_0)$ with $Y$ symmetric is feasible for the dual (12) if and only if
--   $$
--   \begin{pmatrix}Y & \tfrac12(y-\alpha_k p_i)\\ \tfrac12(y-\alpha_k p_i)' & y_0+\alpha_k p_i'Tx-\beta_k\end{pmatrix}\succeq 0\qquad\forall k=1,\dots,K,\ i=1,\dots,N .
--   $$
--   Consequently
--   $$
--   \hat Z_D(x)=\min_{Y,y,y_0}\ Q\cdot Y+\mu'y+y_0\quad\text{s.t. the } NK \text{ linear matrix inequalities above},
--   $$
--   which is the program (15).
--
--   This is the step that makes the dual of the second-stage problem a semidefinite program of polynomial size.
--
--   **Formalization Note** The two feasible sets are stated equal as sets, and the two optimal values (real infima) are then equal.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, pp. 589–590, proof of Theorem 3.2, (15)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic
import Definitions.Def_MinimaxSLP_RhsSDP_Model

namespace MinimaxSLP.RhsSDP

open MeasureTheory Matrix

/-- Proof of Theorem 3.2, pp. 589–590: under `α_k ≥ 0`, complete recourse (Assumption 2),
dual feasibility at the constant `q` (Assumption 3) and Assumption 5, the feasible set of (12)
coincides with that of (15) (one linear matrix inequality per pair `(k, i)`), so
`Ẑ_D(x)` equals the optimal value of (15). -/
theorem dualFeasible12_eq_feasible15 {r d n K N : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (ps : Fin N → Fin r → ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})
    (x : Fin n → ℝ) :
    dualFeasible12 W T q α β x = feasible15 T α β ps x ∧
      ZhatD W T q α β μ Q x = ZhatD15 T α β ps μ Q x := by sorry

end MinimaxSLP.RhsSDP
