-- Prove2me | Theorems.Thm_MultiPriceOnline_Hardness_proposition_4
-- name    : MultiPriceOnline.Hardness.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:08.924515+00:00
-- url     : https://prove2.me/theorems/53f34ee6-9546-4690-9176-a9ffa145e9ad
-- title:
--   Proposition 4, p. 23 — the system (24) has a unique solution with 0 < Bₘ < … < B₂ < B₁ = 1
-- statement:
--   Let $m \ge 1$, let $0 < r^{(1)} < \dots < r^{(m)}$ be a price set, and let $\alpha^{(1)}, \dots, \alpha^{(m)}$ be its booking limits (Proposition 1). Set $B_1 = 1$. Then the system
--
--   $$B_m r^{(m)} e^{-\alpha^{(m)}} = \dots = B_2 r^{(2)} e^{-\alpha^{(2)}} = r^{(1)} e^{-\alpha^{(1)}} \qquad (24)$$
--
--   has a solution $B_2, \dots, B_m$ satisfying $0 < B_m < \dots < B_2 < B_1 = 1$. Any two solutions agree on $B_2, \dots, B_m$.
--
--   The numbers $B_j$ determine the phase lengths $\beta_j = B_j - B_{j+1}$ of the counterexample in §5. Proposition 4 shows that these lengths are positive and sum to one.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 23, Proposition 4, eq. (24); proof p. 46, App. D

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet

namespace MultiPriceOnline.Hardness
theorem proposition_4 {m : ℕ} {r α : ℕ → ℝ} (hm : 1 ≤ m) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) :
    (∃ B : ℕ → ℝ, IsPhaseB m r α B ∧ 0 < B m ∧ ∀ j : ℕ, 2 ≤ j → j ≤ m → B j < B (j - 1)) ∧
    ∀ B B' : ℕ → ℝ, IsPhaseB m r α B → IsPhaseB m r α B' →
      ∀ j : ℕ, 1 ≤ j → j ≤ m → B j = B' j := by sorry
end MultiPriceOnline.Hardness
