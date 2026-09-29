-- Prove2me | Theorems.Thm_GallegoOzerADI_ZeroSetup_J_decreasingDifferences
-- name    : GallegoOzerADI.ZeroSetup.J_decreasingDifferences
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:56:35.933805+00:00
-- url     : https://prove2.me/theorems/545efb8c-df6b-4313-8c9d-47a01cbcf5a6
-- title:
--   Theorem 4, Part 6 — $J_t(x, o_t)$ has decreasing differences in $(x, o_t)$
-- statement:
--   In the inventory model with advance demand information and zero set-up cost, under its standing hypotheses, for every period $t \in \{1, \dots, T\}$ the optimal cost-to-go $(x, o) \mapsto J_t(x, o)$ has decreasing differences in $(x, o)$ (Definition 2): for all $x_1 \ge x_2$ and all observed-demand vectors $o \ge o'$ (componentwise),
--
--   $$J_t(x_1, o) - J_t(x_2, o) \le J_t(x_1, o') - J_t(x_2, o').$$
--
--   Together with Part 4 this propagates decreasing differences backward through the functional equation.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1351, Theorem 4, Part 6

import Mathlib
import Definitions.Def_GallegoOzerADI_ZeroSetup_Model
import Definitions.Def_GallegoOzerADI_ZeroSetup_DecreasingDifferences

open MeasureTheory Filter Topology

namespace GallegoOzerADI.ZeroSetup

/-- Theorem 4, Part 6 (p. 1351): for every period `t ∈ {1, …, T}`, `J_t(x, o_t)` has decreasing
differences in `(x, o_t)` (Definition 2). -/
theorem J_decreasingDifferences {L M : ℕ} (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) :
    DecreasingDifferences (fun x o => P.J t x o) := by sorry

end GallegoOzerADI.ZeroSetup
