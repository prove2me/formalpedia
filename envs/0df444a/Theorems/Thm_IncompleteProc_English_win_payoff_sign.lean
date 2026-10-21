-- Prove2me | Theorems.Thm_IncompleteProc_English_win_payoff_sign
-- name    : IncompleteProc.English.win_payoff_sign
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:25.936971+00:00
-- url     : https://prove2.me/theorems/7e5d5dcb-4fcf-4e8b-be5a-0a5c2d184229
-- title:
--   Proof of Proposition 3, p. 18 (PDF 19) — winning at price x is profitable when x ≥ c and unprofitable when x < c
-- statement:
--   Consider a supplier with first-period cost $c \in [\underline c, \bar c]$ who wins the English auction at price $x \in [\underline c, \bar c]$. He then receives the offer $p_2(\omega, x) = \min\{k(x, \omega), k(c^\star_2(\omega), \omega)\}$ and accepts it iff it covers his cost $k(c, \omega)$. His payoff is
--   $$x - c + \int_\Omega Q \max\{0, p_2(\omega, x) - k(c, \omega)\}\, dG(\omega).$$
--   It is non-negative when $x \ge c$, and strictly negative when $x < c$: in that case he rejects every offer, because $p_2(\omega, x) \le k(x, \omega) < k(c, \omega)$, and he receives $x - c < 0$.
--
--   Against opponents who exit truthfully, a supplier's exit point affects his payoff only through whether he wins and at what price his last opponent quits. So the statement shows that truthful exit, $\beta^E(c) = c$, is a best response.
--
--   **Formalization Note** The reduction of the equilibrium condition to this sign condition is the argument of the proof on p. 18. The price is restricted to the cost range, which contains every price the auction can produce.
-- source:
--   Gretschko & Pollrich, Incomplete Contracts in Dynamic Procurement, ZEW Discussion Paper No. 19-040 (Sept. 2019; SSRN 3466701), p. 18 (PDF 19), proof of Proposition 3 (suppliers' first-period strategy)

import Mathlib
import Definitions.Def_IncompleteProc_English_Model
import Definitions.Def_IncompleteProc_English_Auction

namespace IncompleteProc.English

open MeasureTheory

/-- Proof of Proposition 3 (p. 18): a supplier with cost `c` who wins the English auction at a price
`x ∈ [c̲, c̄]` and then best-responds to the offer `p₂(ω, x)` earns a non-negative payoff if
`x ≥ c` and a negative payoff if `x < c` (in which case he rejects every offer). -/
theorem win_payoff_sign {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) :
    ∀ c ∈ Set.Icc E.clo E.chi, ∀ x ∈ Set.Icc E.clo E.chi,
      (c ≤ x → 0 ≤ E.winPayoff c x) ∧ (x < c → E.winPayoff c x < 0) := by sorry

end IncompleteProc.English
