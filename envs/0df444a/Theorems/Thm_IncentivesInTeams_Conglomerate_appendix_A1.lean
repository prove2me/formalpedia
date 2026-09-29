-- Prove2me | Theorems.Thm_IncentivesInTeams_Conglomerate_appendix_A1
-- name    : IncentivesInTeams.Conglomerate.appendix_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:24:45.266157+00:00
-- url     : https://prove2.me/theorems/12b86e54-825f-4e4d-8882-a37f6001db60
-- title:
--   (A.1): $\bar\omega_i^{II}(\beta^*/\beta_i) + A_i = \bar\omega_0(\beta^*/\beta_i)$
-- statement:
--   Consider a conglomerate model whose component weights are probability weights, a joint strategy $\beta^*$, constants $A_i$, a subunit $i$ and a strategy $\beta_i \in B_i$. Let $W^{II}$ be the incentive structure (3.5) built from $\beta^*$ and the constants $A_i$. Then
--   $$\bar\omega_i^{II}(\beta^*/\beta_i) + A_i = \bar\omega_0(\beta^*/\beta_i),$$
--   where $\bar\omega_i^{II}$ is the expected value of subunit $i$'s payoff under $W^{II}$ and $\bar\omega_0$ is the expected organization payoff.
--
--   Up to the constant $A_i$, a subunit's expected reward under $W^{II}$ equals the expected payoff of the whole organization, whatever strategy the subunit plays while the others follow $\beta^*$. This is the identity to which the paper reduces Theorem 1.
-- source:
--   Groves, Incentives in Teams, Econometrica 41(4), 1973, p. 629, Appendix, PROOF OF THEOREM 1, (A.1), and the two displays at the top of p. 630

import Mathlib
import Definitions.Def_IncentivesInTeams_Conglomerate_Model

namespace IncentivesInTeams.Conglomerate

theorem appendix_A1 {ι : Type*} [Fintype ι] [DecidableEq ι] {S₀ : Type*} [Fintype S₀] {S : ι → Type*}
    [∀ i, Fintype (S i)] {Z₀ : Type*} {Z M₀ M : ι → Type*} {D₀ : Type*} {D : ι → Type*}
    (T : Model S₀ S Z₀ Z M₀ M D₀ D) (hT : T.WeightsOK)
    (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (A : ι → ℝ) (i : ι)
    (b : SubStrategy (S i) (Z i) (M₀ i) (M i) (D i)) (hb : b ∈ T.B i) :
    T.expect (T.WII βs A i (βs.update i b)) + A i = T.expOrgPayoff (βs.update i b) := by sorry

end IncentivesInTeams.Conglomerate
