-- Prove2me | Theorems.Thm_IncompleteProc_English_offer_optimal
-- name    : IncompleteProc.English.offer_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:34.327226+00:00
-- url     : https://prove2.me/theorems/6c042830-a2d0-4847-b7a7-c57d36c14c53
-- title:
--   Proof of Proposition 3, eq. (9), p. 18 (PDF 19) — against the belief F(c)/F(p), the offer min{k(p, ω), k(c⋆2(ω), ω)} is optimal
-- statement:
--   Suppose the English auction ended at price $p \in (\underline c, \bar c]$, so the buyer believes the winner's cost has distribution $F(c)/F(p)$ on $[\underline c, p]$, and the state $\omega$ has realized. An offer $k(c, \omega)$ with cutoff type $c \in [\underline c, p]$ is accepted by the types below $c$. The buyer's problem (9) is
--   $$\max_{c \in [\underline c, p]} Q\big(R - k(c, \omega)\big)\frac{F(c)}{F(p)}.$$
--   The cutoff $\min\{p, c^\star_2(\omega)\}$ solves (9): for every $c \in [\underline c, p]$,
--   $$Q\big(R - k(c, \omega)\big)\frac{F(c)}{F(p)} \le Q\big(R - k(\min\{p, c^\star_2(\omega)\}, \omega)\big)\frac{F(\min\{p, c^\star_2(\omega)\})}{F(p)}.$$
--   The corresponding offer is $k(\min\{p, c^\star_2(\omega)\}, \omega) = \min\{k(p, \omega), k(c^\star_2(\omega), \omega)\} = p_2(\omega, p)$.
--
--   This is the sequential-rationality half of Proposition 3: with only the auction price to go on, the buyer has no incentive to deviate from the offer $p_2$.
--
--   **Formalization Note** The price ranges over $(\underline c, \bar c]$, which contains every price at which the auction can end with positive probability; at $p = \underline c$ the belief $F(c)/F(p)$ is undefined. The belief is the page's Bayes step, stated rather than derived. The page appeals to strict concavity of the objective. That is not needed, and it does not follow from the assumptions; the conclusion is stated as the page gives it.
-- source:
--   Gretschko & Pollrich, Incomplete Contracts in Dynamic Procurement, ZEW Discussion Paper No. 19-040 (Sept. 2019; SSRN 3466701), p. 18 (PDF 19), proof of Proposition 3, eq. (9)

import Mathlib
import Definitions.Def_IncompleteProc_English_Model
import Definitions.Def_IncompleteProc_English_Auction

namespace IncompleteProc.English

open MeasureTheory

/-- Proof of Proposition 3, eq. (9) (p. 18): after an auction that ended at price `p ∈ (c̲, c̄]`, in
every state `ω` the cutoff type `min{p, c⋆₂(ω)}` maximizes the buyer's second-period objective
`Q (R − k(c, ω)) F(c)/F(p)` over `c ∈ [c̲, p]`, and the corresponding offer
`k(min{p, c⋆₂(ω)}, ω)` is `p₂(ω, p) = min{k(p, ω), k(c⋆₂(ω), ω)}`. -/
theorem offer_optimal {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) :
    ∀ p ∈ Set.Ioc E.clo E.chi, ∀ ω,
      (∀ c ∈ Set.Icc E.clo p, E.offerValue ω p c ≤ E.offerValue ω p (min p (E.cStar2 ω))) ∧
      E.offer ω p = E.k (min p (E.cStar2 ω)) ω := by sorry

end IncompleteProc.English
