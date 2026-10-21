-- Prove2me | Theorems.Thm_HiddenRebate_Fixed_contract_star_ic
-- name    : HiddenRebate.Fixed.contract_star_ic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:10.890907+00:00
-- url     : https://prove2.me/theorems/e9f88d9b-29e5-4fe3-a9b3-753f3c6f5df0
-- title:
--   §5.1, p. 12 — under ⟨A∗, F∗⟩ the intermediary always collects r, so truthful reporting is incentive-compatible
-- statement:
--   Let $r \ge 0$ be the hidden rebate and let $\langle A^*, F^*\rangle$ be the contract (15): select $S$ when $z_S \le z_W - r$ and $W$ otherwise, and pay the fee $F^*(z) = r$ exactly when $S$ is selected.
--
--   Then $\langle A^*, F^*\rangle$ is admissible (non-negative, measurable), it satisfies the incentive-compatibility constraint (13), and for every cost pair $x_S, x_W \ge 0$ the intermediary's truthful payoff is
--   $$\pi\big(q; \langle A^*, F^*\rangle\big) = r, \qquad q = (x_S, x_W + r).$$
--
--   Whichever manufacturer is selected, the intermediary receives $r$, either as the fee from the retailer or as the rebate from $W$; this removes the motive to inflate $S$'s quote that the "lowest quote wins" rule creates.
--
--   **Formalization Note** The rebate is assumed non-negative, as the model's "hidden rebate" requires; with $r < 0$ the fee would be negative and the contract inadmissible.
-- source:
--   Fan, Chen & Tang, Mechanism design for managing hidden rebates and inflated quotes of a procurement service provider, SSRN preprint 3514358, p. 12, §5.1 (paragraph after Theorem 1)

import Mathlib
import Definitions.Def_HiddenRebate_Fixed_Model

namespace HiddenRebate.Fixed

/-- §5.1, p. 12: under ⟨A∗, F∗⟩ the intermediary always collects `r`, so (15) is a feasible,
incentive-compatible contract. -/
theorem contract_star_ic (r : ℝ) (hr : 0 ≤ r) :
    Feasible (contractStar r).1 (contractStar r).2 ∧
    IsIC r (contractStar r).1 (contractStar r).2 ∧
    ∀ x : ℝ × ℝ, 0 ≤ x.1 → 0 ≤ x.2 →
      payoff r (contractStar r).1 (contractStar r).2 (quote r x) (quote r x) = r := by sorry

end HiddenRebate.Fixed
