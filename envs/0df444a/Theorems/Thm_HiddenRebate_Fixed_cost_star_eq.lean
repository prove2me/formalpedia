-- Prove2me | Theorems.Thm_HiddenRebate_Fixed_cost_star_eq
-- name    : HiddenRebate.Fixed.cost_star_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:55.374086+00:00
-- url     : https://prove2.me/theorems/8f8fed01-f91e-4e2a-8321-ad7dc6c8668d
-- title:
--   (19), p. 13 — the retailer's expected cost under ⟨A∗, F∗⟩ is E[min{xS, xW} + r]
-- statement:
--   Assume the standing assumptions: $x_S, x_W$ are iid with a law $\mu$ that has a density on $[0,\infty)$ and finite mean, and $r \ge 0$. Under truthful reporting, the retailer's cost $q_{A^*(q)} + F^*(q)$ of the contract (15), at $q = (x_S, x_W + r)$, is integrable, and its expectation (14) equals
--   $$E\big[C(q; \langle A^*, F^*\rangle)\big] = E\big[\min\{x_S, x_W\} + r\big].$$
--
--   The retailer buys from the cheaper manufacturer and pays the intermediary $r$ in every state, as fee or (indirectly) through $W$'s inflated quote. This is the cost that Theorem 1 shows to be optimal for $r < \bar r$, and that Corollary 2 compares with the "lowest quote wins" cost $E(x_W) + r$.
--
--   **Formalization Note** $E[x_S] < \infty$ and $r \ge 0$ are added to the page's assumptions (see the model definition); the expectation is a Bochner integral over $\mu \otimes \mu$.
-- source:
--   Fan, Chen & Tang, Mechanism design for managing hidden rebates and inflated quotes of a procurement service provider, SSRN preprint 3514358, p. 13, eq. (19)

import Mathlib
import Definitions.Def_HiddenRebate_Fixed_Model

namespace HiddenRebate.Fixed

open MeasureTheory

/-- (19), p. 13: under truthful reporting the retailer's expected cost of ⟨A∗, F∗⟩ is
`E[min{xS, xW} + r]`. -/
theorem cost_star_eq (μ : Measure ℝ) (r : ℝ) (hμ : Standing μ r) :
    Integrable (costIntegrand r (contractStar r).1 (contractStar r).2) (μ.prod μ) ∧
    cost μ r (contractStar r).1 (contractStar r).2 = ∫ x, (min x.1 x.2 + r) ∂(μ.prod μ) := by sorry

end HiddenRebate.Fixed
