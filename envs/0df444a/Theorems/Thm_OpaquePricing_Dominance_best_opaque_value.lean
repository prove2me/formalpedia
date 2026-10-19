-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_best_opaque_value
-- name    : OpaquePricing.Dominance.best_opaque_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:58.009696+00:00
-- url     : https://prove2.me/theorems/80620ee7-c173-4ce9-960b-7c3065e5c17f
-- title:
--   Proof of Theorem 1, Case (i): best size-k opaque value
-- statement:
--   Let $v$ be an $N$-item valuation vector and $1\le k\le N$. A pessimistic customer values a subset $S$ at its least-valued item. Among all subsets of size $k$, the greatest such value is the $k$th largest coordinate of $v$:
--
--   $$\max_{|S|=k}\min_{j\in S}v_j=v^{(k)}.$$
--
--   This identifies the best opaque option at each size with an order statistic.
--
--   **Formalization Note** The order statistic sorts coordinates with multiplicity; it is defined separately from the maximum over subsets.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), proof of Theorem 1, Case (i), pp. 18–19

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OpaquePricing.Dominance

theorem best_opaque_value {N : ℕ} (v : Fin N → ℝ) (k : ℕ)
    (hk0 : 1 ≤ k) (hkN : k ≤ N) :
    (⨆ S : {S : Finset (Fin N) // S.card = k}, pessValue v S.val) =
      orderStat v (k - 1) := by sorry

end OpaquePricing.Dominance
