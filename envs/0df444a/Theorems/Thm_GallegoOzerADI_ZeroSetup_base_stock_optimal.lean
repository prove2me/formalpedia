-- Prove2me | Theorems.Thm_GallegoOzerADI_ZeroSetup_base_stock_optimal
-- name    : GallegoOzerADI.ZeroSetup.base_stock_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:54:53.582833+00:00
-- url     : https://prove2.me/theorems/bb337cd1-2515-467e-a6cb-356b8d3f3376
-- title:
--   Theorem 4, Part 2 — a state-dependent base-stock policy with level $y_t(o_t)$ (Eq. (11)) is optimal
-- statement:
--   In the inventory model with advance demand information and zero set-up cost, under its standing hypotheses, fix a period $t \in \{1, \dots, T\}$ and a vector $o_t$ of observed demands beyond the protection period. Then the smallest minimizer
--
--   $$y_t(o_t) = \min\{y : V_t(y, o_t) = \min_x V_t(x, o_t)\} \tag{11}$$
--
--   exists, and ordering up to it is optimal: for every modified inventory position $x$,
--
--   $$J_t(x, o_t) = V_t\big(\max(y_t(o_t), x),\, o_t\big).$$
--
--   That is, an optimal ordering policy is a state-dependent base-stock policy: if $x < y_t(o_t)$ raise the position to $y_t(o_t)$, otherwise do not order.
--
--   **Formalization Note.** "An optimal ordering policy is a base-stock policy" is expressed through the functional equation: the infimum $\inf_{y \ge x} V_t(y, o_t)$ is attained at $\max(y_t(o_t), x)$ (the paper's Eq. (14), p. 1357). No policy or trajectory objects are introduced.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1351, Theorem 4, Part 2, Eq. (11); p. 1357, Eq. (14)

import Mathlib
import Definitions.Def_GallegoOzerADI_ZeroSetup_Model

open MeasureTheory Filter Topology

namespace GallegoOzerADI.ZeroSetup

/-- Theorem 4, Part 2 (p. 1351, Eqs. (11) and (14)): for every period `t ∈ {1, …, T}` and every
fixed vector `o_t`, the smallest minimizer `y_t(o_t)` of `V_t(·, o_t)` exists, and ordering up to it
is optimal: `J_t(x, o_t) = V_t(max(y_t(o_t), x), o_t)` for every `x`. -/
theorem base_stock_optimal {L M : ℕ} (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ∃ y : ℝ, IsLeastMinimizer (fun z => P.V t z o) y ∧
      ∀ x : ℝ, P.J t x o = P.V t (max y x) o := by sorry

end GallegoOzerADI.ZeroSetup
