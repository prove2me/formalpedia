-- Prove2me | Theorems.Thm_IncompleteProc_English_english_utility
-- name    : IncompleteProc.English.english_utility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:35.553862+00:00
-- url     : https://prove2.me/theorems/969c9d39-a4f5-48f7-b407-1823c8e57b11
-- title:
--   Proof of Proposition 3, pp. 18–19 (PDF 19–20) — English-auction profit U(c) = ∫_c^{c⋆1} H + ∫_c^{c⋆1} H ∫_{Ω(s)} Q k_c dG ds
-- statement:
--   In the English auction with reserve $c^\star_1$ followed by the offer $p_2$, let the other suppliers exit truthfully, and let $H(s) = (1 - F(s))^{n-1}$. The interim expected profit $U(c)$ of a supplier with cost $c$ (winning at the price $p_1$, then accepting $p_2$ iff profitable) is, for $c \in [\underline c, c^\star_1]$,
--   $$U(c) = \int_c^{c^\star_1} H(s)\, ds + \int_c^{c^\star_1} H(s) \int_{\Omega(s)} Q\, k_c(s, \omega)\, dG(\omega)\, ds,$$
--   and $U(c) = 0$ for $c \in (c^\star_1, \bar c]$.
--
--   This is the profit of type $c$ in the optimal direct mechanism of Proposition 1. Since the English auction also implements that mechanism's allocation, it follows that the auction gives the buyer the maximal surplus.
--
--   **Formalization Note** The profit is computed for each supplier $i$ with the other coordinates of the cost profile drawn from the i.i.d. law. The statement for $c > c^\star_1$ (the supplier never wins) is the page's implicit complement.
-- source:
--   Gretschko & Pollrich, Incomplete Contracts in Dynamic Procurement, ZEW Discussion Paper No. 19-040 (Sept. 2019; SSRN 3466701), pp. 18–19 (PDF 19–20), proof of Proposition 3 (supplier's expected profit U(c))

import Mathlib
import Definitions.Def_IncompleteProc_English_Model
import Definitions.Def_IncompleteProc_English_Auction

namespace IncompleteProc.English

open MeasureTheory

/-- Proof of Proposition 3 (pp. 18–19): when the other suppliers exit truthfully, the interim
expected profit of supplier `i` with cost `c ≤ c⋆₁` in the English auction followed by the offer
`p₂` is `U(c) = ∫_c^{c⋆₁} H(s) ds + ∫_c^{c⋆₁} H(s) ∫_{Ω(s)} Q k_c(s, ω) dG(ω) ds`, and it is `0`
for `c > c⋆₁`. -/
theorem english_utility {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) (i : Fin E.n) :
    (∀ c ∈ Set.Icc E.clo E.cStar1,
      E.englishU i c = (∫ s in c..E.cStar1, E.H s) +
        ∫ s in c..E.cStar1, E.H s * ∫ ω in E.contSet s, E.Q * E.kc s ω ∂E.G) ∧
    (∀ c ∈ Set.Ioc E.cStar1 E.chi, E.englishU i c = 0) := by sorry

end IncompleteProc.English
