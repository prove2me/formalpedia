-- Prove2me | Theorems.Thm_GallegoOzerADI_ZeroSetup_V_decreasingDifferences
-- name    : GallegoOzerADI.ZeroSetup.V_decreasingDifferences
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:56:01.343629+00:00
-- url     : https://prove2.me/theorems/e41420ca-b62e-41aa-b582-688ef8b25540
-- title:
--   Theorem 4, Part 4 — $V_t(x, o_t)$ has decreasing differences in $(x, o_t)$
-- statement:
--   In the inventory model with advance demand information and zero set-up cost, under its standing hypotheses, for every period $t \in \{1, \dots, T\}$ the function $(x, o) \mapsto V_t(x, o)$ has decreasing differences in $(x, o)$ (Definition 2): for all $x_1 \ge x_2$ and all observed-demand vectors $o \ge o'$ (componentwise),
--
--   $$V_t(x_1, o) - V_t(x_2, o) \le V_t(x_1, o') - V_t(x_2, o').$$
--
--   Higher observed demand beyond the protection period makes raising the inventory position relatively cheaper; this is the property from which monotonicity of the base-stock level in $o_t$ follows.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1351, Theorem 4, Part 4

import Mathlib
import Definitions.Def_GallegoOzerADI_ZeroSetup_Model
import Definitions.Def_GallegoOzerADI_ZeroSetup_DecreasingDifferences

open MeasureTheory Filter Topology

namespace GallegoOzerADI.ZeroSetup

/-- Theorem 4, Part 4 (p. 1351): for every period `t ∈ {1, …, T}`, `V_t(x, o_t)` has decreasing
differences in `(x, o_t)` (Definition 2). -/
theorem V_decreasingDifferences {L M : ℕ} (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) :
    DecreasingDifferences (fun x o => P.V t x o) := by sorry

end GallegoOzerADI.ZeroSetup
