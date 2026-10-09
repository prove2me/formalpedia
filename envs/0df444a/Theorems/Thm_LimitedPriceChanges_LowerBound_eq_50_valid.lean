-- Prove2me | Theorems.Thm_LimitedPriceChanges_LowerBound_eq_50_valid
-- name    : LimitedPriceChanges.LowerBound.eq_50_valid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:33.171721+00:00
-- url     : https://prove2.me/theorems/b59ba5c8-ffff-4c9c-97f8-94e9332dbefc
-- title:
--   (50), p. 36 — the hierarchical parameters are valid for large horizons
-- statement:
--   For each integer $m\ge1$, there is a horizon threshold $T_1$ such that every sign vector $\zeta\in\{\pm1\}^{m+1}$ produces an admissible parameter for every $T\ge T_1$:
--   $$z_\zeta\in[1/6,5/6].$$
--   This ensures that the finite parameter family used for the lower bound stays inside the Bernoulli instance.
--
--   **Formalization Note** The paper says this holds for all horizons, but at $m=1,T=1,\zeta=(1,1)$ it gives $z_\zeta=1$. The large-horizon threshold is the necessary correction.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), p. 36, (50), sentence after (50)

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_Hierarchy

namespace LimitedPriceChanges.LowerBound

/-- (50), p. 36: the constructed parameters lie in the admissible interval for large T. -/
theorem eq_50_valid (m : ℕ) (hm : 1 ≤ m) :
    ∃ T1 : ℕ, ∀ T ≥ T1, ∀ ζ : SignVector m,
      zz m T ζ ∈ Set.Icc (1 / 6 : ℝ) (5 / 6 : ℝ) := by sorry

end LimitedPriceChanges.LowerBound
