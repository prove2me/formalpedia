-- Prove2me | Theorems.Thm_InventoryBounds_stationary_value_derivative
-- name    : InventoryBounds.stationary_value_derivative
-- status  : Open
-- author  : @visuddhi
-- created : 2026-10-08T15:32:59.273782+00:00
-- url     : https://prove2.me/theorems/ea82a240-12bd-4bb8-ad4b-eb821127c30f
-- title:
--   Theorem 3.7 — derivative of the explicit value polynomial
-- statement:
--   For every natural horizon and real rho, the derivative of the explicit value polynomial is -T+2 sum rho^k+(2rho-1) sum k rho^(k-1). This is a polynomial identity, not a global optimal-value formula outside the hard-family parameter range.
-- source:
--   Hanzhang Qin, David Simchi-Levi, Ruihao Zhu, Information Limits of Multistage Inventory Control: Learning, Valuation, and Censoring, arXiv:2609.37380v1 (29 September 2026), https://arxiv.org/abs/2609.37380v1, Theorem 3.7, equation (7)

import Definitions.Def_InventoryBounds_StationaryValuation

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InventoryBounds

theorem stationary_value_derivative (T : ℕ) (ρ : ℝ) :
    HasDerivAt (valueFormula T) (valueDerivative T ρ) ρ := by sorry

end InventoryBounds
