-- Prove2me | Theorems.Thm_MechanismDesign_DominantExamples_auction_epir_iff
-- name    : MechanismDesign.DominantExamples.auction_epir_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:29:50.399242+00:00
-- url     : https://prove2.me/theorems/84a447db-7e43-498c-850d-2ffa702c6b80
-- title:
--   Proposition 4.3 — ex post individual rationality binds at the lowest type
-- statement:
--   Let $(q, t_1, \dots, t_N)$ be a dominant strategy incentive-compatible direct auction mechanism on $\Theta = [\underline\theta,\bar\theta]^I$. It is ex post individually rational (Definition 4.2) if and only if for every buyer $i$ and every $\theta_{-i} \in \Theta_{-i}$
--   $$t_i(\underline\theta,\theta_{-i}) \le \underline\theta\, q_i(\underline\theta,\theta_{-i}).$$
--
--   Under dominant strategy incentive compatibility it thus suffices to check the participation constraint of the lowest type, separately for each profile of the other buyers' types.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.81, Proposition 4.3

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_Auction

namespace MechanismDesign.DominantExamples

/-- Proposition 4.3, p.81. A dominant strategy incentive-compatible direct auction mechanism
is ex post individually rational if and only if for every buyer `i` and every
`θ_{-i} ∈ Θ_{-i}`: `t_i(θ̲, θ_{-i}) ≤ θ̲ q_i(θ̲, θ_{-i})`. -/
theorem auction_epir_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : AuctionSetting}
    (M : AuctionMechanism E ι) (hM : M.IsDSIC) :
    M.IsEPIR ↔ ∀ i, ∀ θ ∈ E.typeSpace ι,
      M.t i (Function.update θ i E.lo) ≤ E.lo * M.q i (Function.update θ i E.lo) := by sorry

end MechanismDesign.DominantExamples
