-- Prove2me | Theorems.Thm_LimitedPriceChanges_LowerBound_separation
-- name    : LimitedPriceChanges.LowerBound.separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:44.299975+00:00
-- url     : https://prove2.me/theorems/5ab7474f-ecf6-4767-b990-428cbc96b216
-- title:
--   p. 37 — differing signs separate the constructed parameters
-- statement:
--   For each $m\ge1$, once $T$ is sufficiently large, if two sign vectors differ at coordinate $\ell$, their constructed parameters satisfy
--   $$|z_\zeta-z_{\zeta'}|\ge\varepsilon_\ell/8.$$
--   This separation turns a mistaken sign prediction into a quantitative parameter error.
--
--   **Formalization Note** The intermediate expression printed on p. 37 has a coefficient/index slip. The stated final lower bound is the part used here, for all sign vectors and all coordinates.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), p. 37, after (56), before (57)

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_Hierarchy

namespace LimitedPriceChanges.LowerBound

/-- p. 37, after (56): different l-th bits force epsilon_l-scale separation. -/
theorem separation (m : ℕ) (hm : 1 ≤ m) :
    ∃ T2 : ℕ, ∀ T ≥ T2, ∀ (ζ ζ' : SignVector m) (l : Fin (m + 1)),
      ζ l ≠ ζ' l → eps m T l / 8 ≤ |zz m T ζ - zz m T ζ'| := by sorry

end LimitedPriceChanges.LowerBound
