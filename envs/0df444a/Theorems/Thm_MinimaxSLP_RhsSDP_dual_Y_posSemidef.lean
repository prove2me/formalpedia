-- Prove2me | Theorems.Thm_MinimaxSLP_RhsSDP_dual_Y_posSemidef
-- name    : MinimaxSLP.RhsSDP.dual_Y_posSemidef
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:47.76699+00:00
-- url     : https://prove2.me/theorems/d5245c32-c65e-4ecb-9f3d-33d16692430c
-- title:
--   §3.1, p. 588 — the dual matrix Y of a feasible point of (12) is positive semidefinite
-- statement:
--   Let $\alpha_k\ge 0$ for all $k$, and let $W,T,q$ satisfy complete recourse (Assumption 2) and $\{p : W'p\le q\}\neq\emptyset$ (Assumption 3 at the constant $q$). If $(Y,y,y_0)$ is feasible for the dual (12) at some $x\in\mathbb R^n$, that is, $Y$ is symmetric and $h'Yh+y'h+y_0\ge\mathbb U(\mathcal Q(h,x))$ for all $h\in\mathbb R^r$, then
--   $$
--   Y\succeq 0 .
--   $$
--
--   This is the observation that the dual feasible set only contains positive semidefinite matrices, used before the separation problem (13).
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 588, §3.1

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic
import Definitions.Def_MinimaxSLP_RhsSDP_Model

namespace MinimaxSLP.RhsSDP

open MeasureTheory Matrix

/-- §3.1, p. 588: the dual matrix `Y` of every feasible point `(Y, y, y₀)` of (12) is positive
semidefinite. Stated under `α_k ≥ 0`, complete recourse (Assumption 2) and
`{π : W′π ≤ q} ≠ ∅` (Assumption 3 at the constant `q`). -/
theorem dual_Y_posSemidef {r d n K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (s : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ)
    (hs : s ∈ dualFeasible12 W T q α β x) :
    s.1.PosSemidef := by sorry

end MinimaxSLP.RhsSDP
