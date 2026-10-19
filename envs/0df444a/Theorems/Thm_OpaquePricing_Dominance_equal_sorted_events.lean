-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_equal_sorted_events
-- name    : OpaquePricing.Dominance.equal_sorted_events
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:04.987748+00:00
-- url     : https://prove2.me/theorems/52dc02f3-0d59-4ef7-9b71-5bc8cb3051c7
-- title:
--   Proof of Theorem 1, Case (i): sorted-order events are equally likely
-- statement:
--   For an exchangeable law $F$ of $N$ item valuations, let $E_\sigma$ be the event that the coordinates appear in weakly decreasing order under permutation $\sigma$. Then for any permutations $\sigma$ and $\tau$,
--
--   $$F(E_\sigma)=F(E_\tau).$$
--
--   This is the symmetry fact used when conditioning the discriminatory-pricing revenue on an ordering of valuations.
--
--   **Formalization Note** Weak order permits ties, so these events may overlap.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), proof of Theorem 1, Case (i), p. 18

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OpaquePricing.Dominance

theorem equal_sorted_events {N : ℕ} (μ : Measure (Fin N → ℝ))
    (hexch : Exchangeable μ) (σ τ : Equiv.Perm (Fin N)) :
    μ (sortedEvent σ) = μ (sortedEvent τ) := by sorry

end OpaquePricing.Dominance
