-- Prove2me | Theorems.Thm_InventoryBounds_stationary_value_separation
-- name    : InventoryBounds.stationary_value_separation
-- status  : Open
-- author  : @visuddhi
-- created : 2026-10-08T15:33:39.54898+00:00
-- url     : https://prove2.me/theorems/f6cc5303-881b-4839-a03b-ef885401baff
-- title:
--   Theorem 3.7 — separation of the two hard-instance values
-- statement:
--   For T at least 8 and 0<epsilon<=T/1024, the value polynomial at rhoPlus exceeds its value at rhoMinus by at least 4epsilon, with rhoPlus/Minus=1-1/(2T) +/- 128epsilon/T^2.
-- source:
--   Hanzhang Qin, David Simchi-Levi, Ruihao Zhu, Information Limits of Multistage Inventory Control: Learning, Valuation, and Censoring, arXiv:2609.37380v1 (29 September 2026), https://arxiv.org/abs/2609.37380v1, Theorem 3.7, proof

import Definitions.Def_InventoryBounds_StationaryValuation

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InventoryBounds

theorem stationary_value_separation (T : ℕ) (hT : 8 ≤ T) (ε : ℝ)
    (hε : 0 < ε) (hεT : ε ≤ (T : ℝ) / 1024) :
    4 * ε ≤ valueFormula T (rhoPlus T ε) - valueFormula T (rhoMinus T ε) := by sorry

end InventoryBounds
