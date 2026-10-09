-- Prove2me | Theorems.Thm_LimitedPriceChanges_LowerBound_eq_57_per_period
-- name    : LimitedPriceChanges.LowerBound.eq_57_per_period
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:58.115375+00:00
-- url     : https://prove2.me/theorems/42200056-a5a9-4f30-8dc6-25532421ce12
-- title:
--   (57), p. 37 — a wrong sign costs at least 10⁻⁴ε² per period
-- statement:
--   For each $m\ge1$, all sufficiently large $T$, every nearest-instance selection $\widehat\zeta$, every price $p\in[1,6]$, and every true sign vector $\zeta^*$: if $\widehat\zeta_\ell(p)\ne\zeta^*_\ell$, then
--   $$G^*(z_{\zeta^*})-r_{z_{\zeta^*}}(p)\ge10^{-4}\varepsilon_\ell^2.$$
--   This is the one-period bound summed over price segments in display (57).
--
--   **Formalization Note** The segment lengths and final-segment subtraction in the printed display are omitted; the item states its pointwise ingredient, which has the same $10^{-4}$ constant.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), p. 37, (57), pointwise inequality behind the display

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_Hierarchy

namespace LimitedPriceChanges.LowerBound

/-- Pointwise regret inequality used in (57), p. 37. -/
theorem eq_57_per_period (m : ℕ) (hm : 1 ≤ m) :
    ∃ T3 : ℕ, ∀ T ≥ T3, ∀ (zsel : ℝ → SignVector m),
      IsNearest m T zsel → ∀ (p : ℝ), p ∈ Set.Icc (1 : ℝ) 6 →
      ∀ (ζstar : SignVector m) (l : Fin (m + 1)),
      zsel p l ≠ ζstar l →
      (1 / 10000 : ℝ) * (eps m T l) ^ 2 ≤
        Gstar (zz m T ζstar) - rev p (zz m T ζstar) := by sorry

end LimitedPriceChanges.LowerBound
