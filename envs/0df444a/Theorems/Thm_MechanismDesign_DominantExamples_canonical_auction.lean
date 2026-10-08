-- Prove2me | Theorems.Thm_MechanismDesign_DominantExamples_canonical_auction
-- name    : MechanismDesign.DominantExamples.canonical_auction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:29:47.54426+00:00
-- url     : https://prove2.me/theorems/3c1739df-f90e-4b55-9fe7-b5c1dfa259b3
-- title:
--   Proposition 4.4 — canonical auctions are dominant strategy IC and ex post IR
-- statement:
--   Let $(q, t_1, \dots, t_N)$ be a canonical auction (Definition 4.3) on $\Theta = [\underline\theta,\bar\theta]^I$: for strictly increasing continuous $\psi_i$, the good goes with equal probability $1/n$ to the $n$ buyers with the highest nonnegative value of $\psi_i(\theta_i)$, and a winning buyer pays $1/n$ times the lowest type with which she would still have won with positive probability. Then the mechanism is dominant strategy incentive-compatible and ex post individually rational, and the lowest type obtains zero utility: for every buyer $i$,
--   $$u_i(\underline\theta,\theta_{-i}) = 0 \quad\text{for all } \theta_{-i} \in \Theta_{-i},$$
--   where $u_i(\theta) = \theta_i q_i(\theta) - t_i(\theta)$.
--
--   With $\psi_i(\theta_i) = \theta_i$ this is the second price auction; with the virtual valuations of §3.2 it shows that an expected-revenue-maximizing auction can be implemented in dominant strategies.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.83, Proposition 4.4

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_Auction

namespace MechanismDesign.DominantExamples

/-- Proposition 4.4, p.83. Every canonical auction is dominant strategy incentive-compatible
and ex post individually rational. Moreover, for every buyer `i`, `u_i(θ̲, θ_{-i}) = 0` for all
`θ_{-i} ∈ Θ_{-i}`. -/
theorem canonical_auction {ι : Type*} [Fintype ι] [DecidableEq ι] {E : AuctionSetting}
    (M : AuctionMechanism E ι) (hM : M.IsCanonical) :
    M.IsDSIC ∧ M.IsEPIR ∧
      ∀ i, ∀ θ ∈ E.typeSpace ι, M.u i (Function.update θ i E.lo) = 0 := by sorry

end MechanismDesign.DominantExamples
