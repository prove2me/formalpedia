-- Prove2me | Theorems.Thm_MinBuying_triangular_price_raising
-- name    : MinBuying.triangular_price_raising
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:26:27.517157+00:00
-- url     : https://prove2.me/theorems/1420a8e2-52c9-4e9a-916d-a085e2cb59cb
-- title:
--   Raising active triangular prices up to their caps
-- statement:
--   Let $I$ be a finite independent triangular-valuation instance with positive parameters and caps $v_i$. Suppose nonnegative price vectors $p,q$ satisfy $p_i\le q_i$ for every item and $q_i\le v_i$ whenever $p_i\le v_i$. Then
--
--   $$R_I(p)\le R_I(q).$$
--
--   Thus raising any active triangular item's price while remaining at or below its cap cannot lower expected min-buying revenue. Items whose original prices already exceed their caps remain inactive. This supports finite candidate sets and attainment of the pricing optima.
-- source:
--   Cui, Hamilton, Lamperski, and Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133, pp.7–9, min-buying model and revenue identities; pp.18–19, equations (11)–(13). Auxiliary price-monotonicity lemma derived during formalization.

import Definitions.Def_MinBuying_Triangular

namespace MinBuying

/-- Raising an active triangular item's price without passing its cap weakly
increases min-buying revenue. Prices already above their caps remain inactive. -/
theorem triangular_price_raising (n : ℕ) (I : TriangularInstance n)
    (p q : Prices n) (hp : FeasiblePrices p) (hq : FeasiblePrices q)
    (hpq : ∀ i, p i ≤ q i)
    (hcap : ∀ i, p i ≤ I.cap i → q i ≤ I.cap i) :
    Revenue (triangularJoint I) p ≤ Revenue (triangularJoint I) q := by
  sorry

end MinBuying
