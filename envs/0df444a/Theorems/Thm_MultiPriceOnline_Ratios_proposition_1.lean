-- Prove2me | Theorems.Thm_MultiPriceOnline_Ratios_proposition_1
-- name    : MultiPriceOnline.Ratios.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:28.25198+00:00
-- url     : https://prove2.me/theorems/f482eb59-e214-4cd5-a883-9e1ff6d735e3
-- title:
--   Proposition 1, p. 13 — the booking limits (7) and the Ball–Queyranne limits (8) exist and are unique
-- statement:
--   Let $m \ge 1$ and let $0 < r^{(1)} < \dots < r^{(m)}$ be a price set. Then:
--
--   1. there exist positive $\alpha^{(1)}, \dots, \alpha^{(m)}$ summing to $1$ that satisfy
--   $$1 - e^{-\alpha^{(1)}} = \frac{1 - e^{-\alpha^{(j)}}}{1 - r^{(j-1)}/r^{(j)}}, \qquad j = 2, \dots, m, \qquad (7)$$
--   and any two such families coincide;
--   2. there exist positive $\sigma^{(1)}, \dots, \sigma^{(m)}$ summing to $1$ that satisfy
--   $$\sigma^{(1)} = \frac{\sigma^{(j)}}{1 - r^{(j-1)}/r^{(j)}}, \qquad j = 2, \dots, m, \qquad (8)$$
--   and any two such families coincide.
--
--   This is what makes $F(\mathcal P) = 1 - e^{-\alpha^{(1)}}$ and $G(\mathcal P) = \sigma^{(1)}$ well defined, and it justifies stating every other result of the mission for an arbitrary family satisfying (7) resp. (8).
--
--   **Formalization Note** Uniqueness is stated on the indices $1, \dots, m$ (the values of the functions elsewhere are irrelevant). The paper also says the $\sigma$'s are a *different* set from the $\alpha$'s; that remark is not part of the statement, since for $m = 1$ both families equal $1$.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 13, Proposition 1, (7)–(8)

import Mathlib
import Definitions.Def_MultiPriceOnline_Ratios_Setting

namespace MultiPriceOnline.Ratios

open Finset

theorem proposition_1 (m : ℕ) (hm : 1 ≤ m) (r : ℕ → ℝ) (hr : MultiPriceOnline.Balance.IsPriceSet m r) :
    ((∃ α : ℕ → ℝ, MultiPriceOnline.Balance.IsBookingLimits m r α) ∧
      ∀ α α' : ℕ → ℝ, MultiPriceOnline.Balance.IsBookingLimits m r α → MultiPriceOnline.Balance.IsBookingLimits m r α' →
        ∀ j ∈ Icc 1 m, α j = α' j) ∧
    ((∃ σ : ℕ → ℝ, MultiPriceOnline.Balance.IsBQLimits m r σ) ∧
      ∀ σ σ' : ℕ → ℝ, MultiPriceOnline.Balance.IsBQLimits m r σ → MultiPriceOnline.Balance.IsBQLimits m r σ' →
        ∀ j ∈ Icc 1 m, σ j = σ' j) := by sorry

end MultiPriceOnline.Ratios
