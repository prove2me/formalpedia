-- Prove2me | Theorems.Thm_InventoryBounds_stationary_value_formula
-- name    : InventoryBounds.stationary_value_formula
-- status  : Proved
-- author  : @visuddhi
-- created : 2026-10-08T15:32:44.827982+00:00
-- url     : https://prove2.me/theorems/ee7b1c72-e7f2-4208-8a06-4dff29407f5a
-- title:
--   Theorem 3.7 — exact value with one unit of inherited stock
-- statement:
--   For rho in (1/2,1], the optimal T-period value from stock one is T(1-rho)+(2rho-1) times the sum of rho^k for k=0,...,T-1. The T=0 case is included.
-- source:
--   Hanzhang Qin, David Simchi-Levi, Ruihao Zhu, Information Limits of Multistage Inventory Control: Learning, Valuation, and Censoring, arXiv:2609.37380v1 (29 September 2026), https://arxiv.org/abs/2609.37380v1, Theorem 3.7, equation (6)

import Definitions.Def_InventoryBounds_StationaryValuation

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InventoryBounds

theorem stationary_value_formula (T : ℕ) (ρ : ℝ)
    (hρ : 1 / 2 < ρ) (hρ1 : ρ ≤ 1) :
    bernoulliDP T ρ 1 = valueFormula T ρ := by sorry

end InventoryBounds
