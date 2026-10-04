-- Prove2me | Theorems.Thm_IncentivesInTeams_Conglomerate_appendix_A2_center
-- name    : IncentivesInTeams.Conglomerate.appendix_A2_center
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:24:11.276031+00:00
-- url     : https://prove2.me/theorems/fbe45b86-05da-4c9b-bea6-5762137d1cba
-- title:
--   (A.2) for the head's component $j = 0$
-- statement:
--   Consider a conglomerate model whose component weights are probability weights, a joint strategy $\beta^*$, a subunit $i$ and a strategy $\beta_i \in B_i$. Let $\hat y_0$ denote the head's information when $\beta^*/\beta_i$ is played. Then
--   $$E\big[v_0[\delta_0^*(\hat y_0(s)), s_0]\big] = E\big[h_0(\hat y_0(s))\big],$$
--   where $h_0(y_0)$ is the head's own factor of his conditional expectation under $\beta^*$ (model file): the average of $v_0[\delta_0^*(y_0), t]$ over the head's states $t$ with $\zeta_0^*(t) = z_0$, for $y_0 = (z_0, m)$.
--
--   This is (A.2) for the component $j = 0$, which the paper covers by "[the proof for $j = 0$ is strictly analogous]". It is needed because the sum $\sum_{j\ne i}$ in (3.3) runs over $I = \{0, \dots, n\}$ and so includes the head's payoff component.
-- source:
--   Groves, Incentives in Teams, Econometrica 41(4), 1973, p. 630, Appendix, display (A.2) and "[the proof for j = 0 is strictly analogous]"

import Mathlib
import Definitions.Def_IncentivesInTeams_Conglomerate_Model

namespace IncentivesInTeams.Conglomerate

theorem appendix_A2_center {ι : Type*} [Fintype ι] [DecidableEq ι] {S₀ : Type*} [Fintype S₀] {S : ι → Type*}
    [∀ i, Fintype (S i)] {Z₀ : Type*} {Z M₀ M : ι → Type*} {D₀ : Type*} {D : ι → Type*}
    (T : Model S₀ S Z₀ Z M₀ M D₀ D) (hT : T.WeightsOK)
    (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (i : ι)
    (b : SubStrategy (S i) (Z i) (M₀ i) (M i) (D i)) (hb : b ∈ T.B i) :
    T.expect (T.headPayoff (βs.update i b)) =
      T.expect (fun s => T.headFactor βs ((βs.update i b).headInfo s)) := by sorry

end IncentivesInTeams.Conglomerate
