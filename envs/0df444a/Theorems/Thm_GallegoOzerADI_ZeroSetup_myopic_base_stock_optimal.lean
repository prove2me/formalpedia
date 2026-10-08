-- Prove2me | Theorems.Thm_GallegoOzerADI_ZeroSetup_myopic_base_stock_optimal
-- name    : GallegoOzerADI.ZeroSetup.myopic_base_stock_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:57:39.408898+00:00
-- url     : https://prove2.me/theorems/26183372-078d-469c-b0f9-4c8fc70d7d5f
-- title:
--   Theorem 5 — if the myopic levels $y^m_t$ are nondecreasing in $t$, the myopic base-stock policy is optimal
-- statement:
--   Consider the inventory model with advance demand information and zero set-up cost under its standing hypotheses (information horizon $N > L + 1$, convex coercive single-period costs $G_t$ of at most linear growth, discount factors $\alpha_{t+1} > 0$, nonnegative demands with finite means). For each period $t$ let the **myopic level** be the smallest minimizer of the single-period cost,
--
--   $$y^m_t = \min\{y : G_t(y) = \min_x G_t(x)\}.$$
--
--   Suppose $t \mapsto y^m_t$ is nondecreasing on $\{1, \dots, T\}$. Then the myopic policy is optimal: for every period $t \in \{1, \dots, T\}$ and every vector $o_t \ge 0$ of observed demands beyond the protection period, the optimal base-stock level of Eq. (11) is the myopic one,
--
--   $$y_t(o_t) = \min\{y : V_t(y, o_t) = \min_x V_t(x, o_t)\} = y^m_t.$$
--
--   In particular the order-up-to level ignores the advance demand information beyond the protection period, and the dynamic program collapses to a sequence of single-period problems.
--
--   **Formalization Note.** The conclusion is restricted to nonnegative observed-demand vectors $o_t \ge 0$. These are exactly the states the system can reach, since each component is a sum of nonnegative orders, and the paper's proof uses $o_{t,t+L+1} \ge 0$ (to get $x_{t+1} \le y$) without stating it; for a strongly negative $o_{t,t+L+1}$ the statement can fail. Monotonicity of $y^m_t$ is required only on the planning periods $1, \dots, T$. The myopic levels are supplied as a sequence characterised as smallest minimizers of the $G_t$.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1352, Theorem 5 (first sentence) and the definition of y^m_t

import Mathlib
import Definitions.Def_GallegoOzerADI_ZeroSetup_Model

open MeasureTheory Filter Topology

namespace GallegoOzerADI.ZeroSetup

/-- Theorem 5 (p. 1352): if the myopic levels `y^m_t` (the smallest minimizers of `G_t`) are
nondecreasing in `t ∈ {1, …, T}`, then the myopic policy is optimal: for every period
`t ∈ {1, …, T}` and every (reachable, i.e. nonnegative) vector `o_t` of observed demands, the
optimal base-stock level `y_t(o_t)` of Eq. (11) equals `y^m_t`. -/
theorem myopic_base_stock_optimal {L M : ℕ} (P : Model L M) (hP : P.Assumptions)
    (ym : ℕ → ℝ) (hym : ∀ t, 1 ≤ t → t ≤ P.T → IsLeastMinimizer (P.G t) (ym t))
    (hmono : MonotoneOn ym (Set.Icc 1 P.T))
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o : Fin M → ℝ) (ho : 0 ≤ o) :
    IsLeastMinimizer (fun y => P.V t y o) (ym t) := by sorry

end GallegoOzerADI.ZeroSetup
