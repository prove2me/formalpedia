-- Prove2me | Theorems.Thm_InventoryBounds_bernoulli_zero_base_stock_optimal
-- name    : InventoryBounds.bernoulli_zero_base_stock_optimal
-- status  : Open
-- author  : @visuddhi
-- created : 2026-10-08T15:32:24.70768+00:00
-- url     : https://prove2.me/theorems/91968a7e-bc54-4694-affe-0a705809f14b
-- title:
--   Theorem 3.7 — zero-base-stock optimality on the hard family
-- statement:
--   For any finite horizon, real initial backlog state, and zero-demand probability rho in (1/2,1], the Bellman optimal value equals the value of always ordering to max(x,0). Unit holding and shortage costs and Bernoulli demands are fixed by the definitions.
-- source:
--   Hanzhang Qin, David Simchi-Levi, Ruihao Zhu, Information Limits of Multistage Inventory Control: Learning, Valuation, and Censoring, arXiv:2609.37380v1 (29 September 2026), https://arxiv.org/abs/2609.37380v1, Theorem 3.7, proof; Lemma 2.1

import Definitions.Def_InventoryBounds_StationaryValuation

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InventoryBounds

theorem bernoulli_zero_base_stock_optimal (T : ℕ) (ρ x : ℝ)
    (hρ : 1 / 2 < ρ) (hρ1 : ρ ≤ 1) :
    bernoulliDP T ρ x = zeroBaseStockValue T ρ x := by sorry

end InventoryBounds
