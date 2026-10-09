-- Prove2me | Theorems.Thm_InventoryBounds_stationary_value_sensitivity
-- name    : InventoryBounds.stationary_value_sensitivity
-- status  : Open
-- author  : @visuddhi
-- created : 2026-10-08T15:33:19.808986+00:00
-- url     : https://prove2.me/theorems/13dda9a9-f42b-46ef-9576-43183b4a72d4
-- title:
--   Theorem 3.7 — quadratic sensitivity on the rare-demand interval
-- statement:
--   For T at least 8 and rho between 1-5/(8T) and 1-3/(8T), the derivative of the value polynomial is at least T^2/64.
-- source:
--   Hanzhang Qin, David Simchi-Levi, Ruihao Zhu, Information Limits of Multistage Inventory Control: Learning, Valuation, and Censoring, arXiv:2609.37380v1 (29 September 2026), https://arxiv.org/abs/2609.37380v1, Theorem 3.7, proof after equation (7)

import Definitions.Def_InventoryBounds_StationaryValuation

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InventoryBounds

theorem stationary_value_sensitivity (T : ℕ) (hT : 8 ≤ T) (ρ : ℝ)
    (hlo : 1 - 5 / (8 * (T : ℝ)) ≤ ρ)
    (hhi : ρ ≤ 1 - 3 / (8 * (T : ℝ))) :
    (T : ℝ) ^ 2 / 64 ≤ valueDerivative T ρ := by sorry

end InventoryBounds
