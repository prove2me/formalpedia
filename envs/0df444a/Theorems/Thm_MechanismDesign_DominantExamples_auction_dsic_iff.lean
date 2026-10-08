-- Prove2me | Theorems.Thm_MechanismDesign_DominantExamples_auction_dsic_iff
-- name    : MechanismDesign.DominantExamples.auction_dsic_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:29:49.539755+00:00
-- url     : https://prove2.me/theorems/e88513d9-0505-4e9a-a956-894fadc5c407
-- title:
--   Proposition 4.2 — characterization of dominant strategy incentive-compatible auctions
-- statement:
--   Consider a direct auction mechanism $(q, t_1, \dots, t_N)$ on $\Theta = [\underline\theta,\bar\theta]^I$ (Definition 3.1). It is dominant strategy incentive-compatible (Definition 4.1) if and only if for every buyer $i$ and every $\theta_{-i} \in \Theta_{-i}$:
--
--   1. $q_i(\theta_i, \theta_{-i})$ is (weakly) increasing in $\theta_i$ on $[\underline\theta,\bar\theta]$;
--   2. for every $\theta_i \in [\underline\theta,\bar\theta]$,
--   $$t_i(\theta_i,\theta_{-i}) = t_i(\underline\theta,\theta_{-i}) + \big(\theta_i q_i(\theta_i,\theta_{-i}) - \underline\theta\, q_i(\underline\theta,\theta_{-i})\big) - \int_{\underline\theta}^{\theta_i} q_i(x,\theta_{-i})\,dx.$$
--
--   Part 2 is an ex post revenue equivalence statement: the allocation rule and the payments of the lowest type pin down every buyer's payment at every type vector.
--
--   **Formalization Note** "Increasing" is weak monotonicity (`MonotoneOn`), the book's convention (Ch. 2, note 3). The integrand is a function of one variable which is monotone under either side of the equivalence, so the integral is a genuine Riemann integral and no measurability hypothesis is needed.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.81, Proposition 4.2

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_Auction

namespace MechanismDesign.DominantExamples

/-- Proposition 4.2, p.81. A direct auction mechanism `(q, t_1, …, t_N)` is dominant strategy
incentive-compatible if and only if for every buyer `i` and every `θ_{-i} ∈ Θ_{-i}`
(represented by `θ ∈ Θ`, whose `i`-th coordinate is overwritten):
(i) `q_i(θ_i, θ_{-i})` is (weakly) increasing in `θ_i` on `[θ̲, θ̄]`;
(ii) for every `θ_i ∈ [θ̲, θ̄]`,
`t_i(θ_i, θ_{-i}) = t_i(θ̲, θ_{-i}) + (θ_i q_i(θ_i, θ_{-i}) − θ̲ q_i(θ̲, θ_{-i}))
  − ∫_{θ̲}^{θ_i} q_i(x, θ_{-i}) dx`. -/
theorem auction_dsic_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : AuctionSetting}
    (M : AuctionMechanism E ι) :
    M.IsDSIC ↔ ∀ i, ∀ θ ∈ E.typeSpace ι,
      MonotoneOn (fun x => M.q i (Function.update θ i x)) (Set.Icc E.lo E.hi) ∧
      ∀ x ∈ Set.Icc E.lo E.hi,
        M.t i (Function.update θ i x) =
          M.t i (Function.update θ i E.lo)
            + (x * M.q i (Function.update θ i x) - E.lo * M.q i (Function.update θ i E.lo))
            - ∫ y in E.lo..x, M.q i (Function.update θ i y) := by sorry

end MechanismDesign.DominantExamples
