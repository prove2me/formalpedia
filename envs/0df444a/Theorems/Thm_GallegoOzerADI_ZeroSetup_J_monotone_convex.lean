-- Prove2me | Theorems.Thm_GallegoOzerADI_ZeroSetup_J_monotone_convex
-- name    : GallegoOzerADI.ZeroSetup.J_monotone_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:55:20.525195+00:00
-- url     : https://prove2.me/theorems/601e1450-d33a-46cb-ac38-1234f1ddf443
-- title:
--   Theorem 4, Part 3 — $J_t(\cdot, o_t)$ is increasing and convex
-- statement:
--   In the inventory model with advance demand information and zero set-up cost, under its standing hypotheses, for every period $t \in \{1, \dots, T\}$ and every fixed vector $o_t$ of observed demands, the optimal cost-to-go
--
--   $$x \mapsto J_t(x, o_t) = \inf_{y \ge x} V_t(y, o_t)$$
--
--   is an increasing (that is, nondecreasing) convex function of the modified inventory position $x$.
--
--   This property is what carries the induction backward in time: it makes $\mathbb{E}\, J_{t+1}(x_{t+1}, o_{t+1})$ convex and nondecreasing in the order-up-to level of the previous period.
--
--   **Formalization Note.** The paper uses "increasing" for "nondecreasing" (footnote 3, p. 1345); the statement is `Monotone`.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1351, Theorem 4, Part 3

import Mathlib
import Definitions.Def_GallegoOzerADI_ZeroSetup_Model

open MeasureTheory Filter Topology

namespace GallegoOzerADI.ZeroSetup

/-- Theorem 4, Part 3 (p. 1351): for every period `t ∈ {1, …, T}` and every fixed vector `o_t`,
`J_t(·, o_t)` is an increasing (nondecreasing) convex function. -/
theorem J_monotone_convex {L M : ℕ} (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o : Fin M → ℝ) :
    Monotone (fun x => P.J t x o) ∧ ConvexOn ℝ Set.univ (fun x => P.J t x o) := by sorry

end GallegoOzerADI.ZeroSetup
