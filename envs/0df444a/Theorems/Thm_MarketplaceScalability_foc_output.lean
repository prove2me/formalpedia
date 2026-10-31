-- Prove2me | Theorems.Thm_MarketplaceScalability_foc_output
-- name    : MarketplaceScalability.foc_output
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:08.332088+00:00
-- url     : https://prove2.me/theorems/60447f5d-552f-4be7-96fc-645be13e488c
-- title:
--   §2.4 — the first-order condition determines the seller's optimal output (corrected: demand conditions)
-- statement:
--   For every $\tilde c\in(0,\bar c]$ and every fixed fee $\tilde F$, the output $q(\tilde c)$ lies in $J$, satisfies
--   $$
--   (1-\alpha)D(q(\tilde c))=\tilde c,
--   $$
--   and is the unique maximizer over $J$ of $x\mapsto(1-\alpha)R(x)-\tilde c x-\tilde F$.
--
--   This is the sellers' last stage of the game, and it justifies using $q(\cdot)$ as the sellers' response to any service.
--
--   Differences from the source:
--   - correction: D > 0, D′ < 0, D″ ≤ 0, D(0) = ∞ on outputs q ≥ 0 (p.4) → outputs in J = (0, q̄), the signs on J, and (1 − α)D(q) = p solvable in J for every p ∈ (0, c̄]; reason: the printed conditions are unsatisfiable: a positive concave function on (0, ∞) cannot be strictly decreasing, and a concave function on (0, b) cannot tend to +∞ at 0; solvability of the first-order condition is the only use of D(0) = ∞
--   - generalization: α a commission rate, Assumption 2 → 0 ≤ α < 1, and of Assumption 2 only f < F; reason: the argument uses no more, and low-type sellers are absent at μ = 1; every source instance, with α ∈ (0, 1), is covered
--   - encoding: c ∈ (c̲, c̄) with no sign on c̲ (p.6) → 0 < c̲; reason: (1 − α)D(q(c̲)) = c̲ with D > 0 and α < 1 forces c̲ > 0, so no source instance is excluded
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §2.4, p.6

import Mathlib
import Definitions.Def_MarketplaceScalability_Model

namespace MarketplaceScalability

/-- **§2.4, p.6.** Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484: "The optimal output level q(c̃) is therefore determined by the first-order
condition: (1 − α)D(q(c̃)) = c̃".

For `c̃ ∈ (0, c̄]`, `q(c̃)` lies in `J`, satisfies the first-order condition, and is the unique maximizer
on `J` of the seller's objective, whatever the fixed fee `F̃`. -/
theorem foc_output (M : Model) {ct : ℝ} (hct : ct ∈ Set.Ioc 0 M.cbar) (Ft : ℝ) :
    M.q ct ∈ M.J ∧
    (1 - M.α) * M.D (M.q ct) = ct ∧
    IsMaxOn (M.sellerProfit ct Ft) M.J (M.q ct) ∧
    ∀ x ∈ M.J, IsMaxOn (M.sellerProfit ct Ft) M.J x → x = M.q ct := by sorry

end MarketplaceScalability
