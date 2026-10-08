-- Prove2me | Theorems.Thm_MinimaxSLP_RhsSDP_dual_constraint_rewrite
-- name    : MinimaxSLP.RhsSDP.dual_constraint_rewrite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:33.921984+00:00
-- url     : https://prove2.me/theorems/210365d6-312e-4682-9082-f8e46d6255b4
-- title:
--   §3.1, p. 588 — the constraints of (12) rewritten over all pieces k and all dual feasible p
-- statement:
--   Let $\alpha_k\ge 0$ for all $k$, and let $W,T,q$ satisfy complete recourse (Assumption 2) and $\{p : W'p\le q\}\neq\emptyset$ (Assumption 3 at the constant $q$). Fix $x\in\mathbb R^n$ and $(Y,y,y_0)$ with $Y$ symmetric. The following are equivalent:
--
--   1. $(Y,y,y_0)$ is feasible for (12): $h'Yh+y'h+y_0\ge\mathbb U(\mathcal Q(h,x))$ for all $h\in\mathbb R^r$;
--   2. $h'Yh+y'h+y_0\ge\alpha_k\mathcal Q(h,x)+\beta_k$ for all $h\in\mathbb R^r$ and $k=1,\dots,K$;
--   3. for all $h\in\mathbb R^r$, all $p$ with $W'p\le q$ and all $k=1,\dots,K$,
--   $$
--   h'Yh+(y-\alpha_kp)'h+y_0+\alpha_kp'Tx-\beta_k\ge 0 .
--   $$
--
--   The third form removes the inner maximization defining $\mathcal Q$ and is the starting point of both the NP-hardness result and the semidefinite reformulation.
--
--   **Formalization Note** Stated as two equivalences with feasibility for (12), whose definition includes the symmetry of $Y$.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 588, §3.1

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic
import Definitions.Def_MinimaxSLP_RhsSDP_Model

namespace MinimaxSLP.RhsSDP

open MeasureTheory Matrix

/-- The rewriting of the constraints of (12), §3.1, p. 588. Under `α_k ≥ 0`, complete recourse
(Assumption 2) and `{π : W′π ≤ q} ≠ ∅` (Assumption 3 at the constant `q`), a point
`(Y, y, y₀)` with `Y` symmetric is feasible for (12) iff
`h′Yh + y′h + y₀ ≥ α_k 𝒬(h, x) + β_k` for all `h ∈ ℝʳ` and all `k`, iff
`h′Yh + (y − α_k π)′h + y₀ + α_k π′T x − β_k ≥ 0` for all `h ∈ ℝʳ`, all `π` with `W′π ≤ q`
and all `k`. -/
theorem dual_constraint_rewrite {r d n K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (s : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) :
    (s ∈ dualFeasible12 W T q α β x ↔
      s.1.IsSymm ∧ ∀ (h : Fin r → ℝ) (k : Fin K),
        α k * Qval W T q h x + β k ≤ h ⬝ᵥ (s.1 *ᵥ h) + s.2.1 ⬝ᵥ h + s.2.2) ∧
    (s ∈ dualFeasible12 W T q α β x ↔
      s.1.IsSymm ∧ ∀ (h : Fin r → ℝ) (π : Fin r → ℝ) (k : Fin K), Wᵀ *ᵥ π ≤ q →
        0 ≤ h ⬝ᵥ (s.1 *ᵥ h) + (s.2.1 - α k • π) ⬝ᵥ h + s.2.2 + α k * (π ⬝ᵥ (T *ᵥ x)) - β k) := by sorry

end MinimaxSLP.RhsSDP
