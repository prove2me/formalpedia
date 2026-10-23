-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_ladder_revenue
-- name    : OpaquePricing.Dominance.ladder_revenue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:04.825043+00:00
-- url     : https://prove2.me/theorems/5f6a127b-57a6-490c-92d1-fa368e77cf46
-- title:
--   Proof of Theorem 1, Case (ii): both types pay the opaque ladder price
-- statement:
--   Let $N\ge2$, $0\le a<b$, and let a valuation vector have only values $a$ and $b$. Write $U$ for its number of $b$ coordinates. Offer all item and opaque sizes at prices $p^k=a+(N-k)(b-a)/N$. Under either pessimistic or risk-neutral opaque valuation, the sale revenue is
--
--   $$R(v)=\begin{cases}a,&U=0,\\a+\frac{N-U}{N}(b-a),&U\ge1.\end{cases}$$
--
--   This pointwise statement supplies the opaque revenue in the two-value branch. Ties are settled in favor of the higher price.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), proof of Theorem 1, Case (ii), pp. 19–20

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OpaquePricing.Dominance

theorem ladder_revenue {N : ℕ} (hN : 2 ≤ N)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (v : Fin N → ℝ) (hv : ∀ i, v i = a ∨ v i = b)
    (val : (Fin N → ℝ) → Finset (Fin N) → ℝ)
    (hval : val = pessValue ∨ val = rnValue) :
    opqRevenue val (ladder N a b 1) (ladder N a b) v =
      if highCount b v = 0 then a
      else a + (((N : ℝ) - highCount b v) / N) * (b - a) := by sorry

end OpaquePricing.Dominance
