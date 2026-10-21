-- Prove2me | Theorems.Thm_IncompleteProc_English_proposition_3
-- name    : IncompleteProc.English.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:33.228347+00:00
-- url     : https://prove2.me/theorems/552d84f8-cd9d-4d24-85e3-ed2255c52503
-- title:
--   Proposition 3, p. 10 (PDF 11) — English auction with reserve c⋆1 and offer min{k(p1,ω), k(c⋆2(ω),ω)} is an equilibrium and attains the optimal complete-contract buyer surplus
-- statement:
--   In the two-period procurement model, suppose the buyer cannot write complete contracts. She runs an English auction in period 1 with reserve price $r^\star = c^\star_1$. After observing the first-period price $p_1$ and the state $\omega$, she makes the winner the take-it-or-leave-it offer
--   $$p_2(\omega, p_1) = \min\{k(p_1, \omega), k(c^\star_2(\omega), \omega)\}.$$
--   Then the following hold.
--   1. **Suppliers exit truthfully.** For all $c, x \in [\underline c, \bar c]$, a supplier with cost $c$ who wins at price $x$ and accepts the offer iff $p_2(\omega, x) \ge k(c, \omega)$ earns a non-negative payoff if $x \ge c$ and a negative payoff if $x < c$. Hence staying in the auction until the price equals one's cost, $\beta^E(c) = c$, is a best response.
--   2. **The offer is optimal for the buyer.** For every price $p \in (\underline c, \bar c]$ and state $\omega$, given her belief $F(c)/F(p)$ on $[\underline c, p]$, the cutoff type $\min\{p, c^\star_2(\omega)\}$ maximizes $Q(R - k(c, \omega))F(c)/F(p)$ over $c \in [\underline c, p]$, and the corresponding offer $k(\min\{p, c^\star_2(\omega)\}, \omega)$ equals $p_2(\omega, p)$.
--   3. **The optimal surplus is attained.** The buyer's expected surplus in this English auction is the greatest buyer surplus over all admissible, incentive-compatible and individually rational complete-contract direct mechanisms:
--   $$\mathrm{BS}^{\mathrm{English}} = \max\{\mathrm{BS}(x, t) : (x, t) \text{ admissible, IC, IR}\}.$$
--
--   The result shows that, in this model, the value of complete contracts is zero. An auction that hides the winner's exact cost from the buyer, followed by spot contracting, gives her the same surplus as the optimal long-term contract.
--
--   **Formalization Note** "Implements the optimal buyer surplus from Proposition 1" is stated as equality with the maximum over the complete-contract mechanism class, attainment included. The equilibrium claims are stated in reduced form: part 1 is the suppliers' best-response condition against truthful opponents, and part 2 is the buyer's problem (9) of the proof. The English-auction surplus is computed from the auction's outcome (winner, price $p_1$, the offer and its acceptance), not from a virtual-surplus formula. Ties go to the lowest index (probability zero). The thresholds are crossing points, and the standing assumptions add $n \ge 1$, measurability in $\omega$ and boundedness of $k$, as explained in the model definition.
-- source:
--   Gretschko & Pollrich, Incomplete Contracts in Dynamic Procurement, ZEW Discussion Paper No. 19-040 (Sept. 2019; SSRN 3466701), p. 10 (PDF 11), Proposition 3; pp. 18–19 (PDF 19–20), proof of Proposition 3

import Mathlib
import Definitions.Def_IncompleteProc_English_Model
import Definitions.Def_IncompleteProc_English_Auction

namespace IncompleteProc.English

open MeasureTheory

/-- Proposition 3 (p. 10): the English auction with reserve `r⋆ = c⋆₁` followed by the
take-it-or-leave-it offer `p₂(ω, p₁) = min{k(p₁, ω), k(c⋆₂(ω), ω)}` is an equilibrium and implements
the optimal buyer surplus of Proposition 1:
(a) truthful exit `β^E(c) = c` is a best response — winning at a price `x` is profitable when
`x ≥ c` and unprofitable when `x < c` (the winner accepts iff `p₂ ≥ k(c, ω)`);
(b) the offer `p₂` is optimal for the buyer given her belief `F(c)/F(p)` on `[c̲, p]`;
(c) the buyer's expected surplus in the English auction is the greatest buyer surplus over all
admissible, incentive-compatible, individually rational complete-contract direct mechanisms. -/
theorem proposition_3 {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) :
    (∀ c ∈ Set.Icc E.clo E.chi, ∀ x ∈ Set.Icc E.clo E.chi,
        (c ≤ x → 0 ≤ E.winPayoff c x) ∧ (x < c → E.winPayoff c x < 0)) ∧
    (∀ p ∈ Set.Ioc E.clo E.chi, ∀ ω,
        (∀ c ∈ Set.Icc E.clo p, E.offerValue ω p c ≤ E.offerValue ω p (min p (E.cStar2 ω))) ∧
        E.offer ω p = E.k (min p (E.cStar2 ω)) ω) ∧
    IsGreatest E.feasibleSurplus E.englishSurplus := by sorry

end IncompleteProc.English
