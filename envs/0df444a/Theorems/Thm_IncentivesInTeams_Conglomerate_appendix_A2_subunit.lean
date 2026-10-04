-- Prove2me | Theorems.Thm_IncentivesInTeams_Conglomerate_appendix_A2_subunit
-- name    : IncentivesInTeams.Conglomerate.appendix_A2_subunit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:23:38.256982+00:00
-- url     : https://prove2.me/theorems/034f23d3-660d-4d5c-bd6a-70f186d0d413
-- title:
--   (A.2) for a subunit $j \ne i$: expected payoff under $\beta^*/\beta_i$ equals the expected conditional expectation
-- statement:
--   Consider a conglomerate model whose component weights are probability weights, a joint strategy $\beta^*$, a subunit $i$, a strategy $\beta_i \in B_i$, and a subunit $j \ne i$. Let $\hat y$ denote the information functions when $\beta^*/\beta_i$ is played. Then
--   $$E\big[v_j[\delta_j^*(\hat y_j(s)), \delta_0^*(\hat y_0(s)); s_j]\big] = E\big[h_j(\hat y_0(s))\big],$$
--   where $h_j(y_0)$ is subunit $j$'s factor of the head's conditional expectation under $\beta^*$ (model file): the average of $v_j[\delta_j^*(\zeta_j^*(t), \gamma_0^{j*}(z_0)), \delta_0^*(y_0); t]$ over the states $t$ of $S_j$ whose message under $\beta^*$ is the one recorded in $y_0 = (z_0, m)$.
--
--   This is equation (A.2) of the paper for a subunit $j \ne i$, with its right-hand side $E[E\{v_j[\delta_j^*(y_j^*), \delta_0^*(y_0^*); s_j] \mid y_0^*(s) = \hat y_0\}]$ in the factorized form. Together with the head's analogue it gives (A.1).
--
--   **Formalization Note.** Under $\beta^*/\beta_i$ the strategy of subunit $j \ne i$ and the head's strategy are those of $\beta^*$, so the left-hand side is the $j$-th payoff component under $\beta^*/\beta_i$. Information follows the one-exchange protocol of the model file.
-- source:
--   Groves, Incentives in Teams, Econometrica 41(4), 1973, p. 630, Appendix, display (A.2) and the l.h.s. (A.2) chain

import Mathlib
import Definitions.Def_IncentivesInTeams_Conglomerate_Model

namespace IncentivesInTeams.Conglomerate

theorem appendix_A2_subunit {ι : Type*} [Fintype ι] [DecidableEq ι] {S₀ : Type*} [Fintype S₀] {S : ι → Type*}
    [∀ i, Fintype (S i)] {Z₀ : Type*} {Z M₀ M : ι → Type*} {D₀ : Type*} {D : ι → Type*}
    (T : Model S₀ S Z₀ Z M₀ M D₀ D) (hT : T.WeightsOK)
    (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (i : ι)
    (b : SubStrategy (S i) (Z i) (M₀ i) (M i) (D i)) (hb : b ∈ T.B i) (j : ι) (hji : j ≠ i) :
    T.expect (T.subPayoff (βs.update i b) j) =
      T.expect (fun s => T.subFactor βs j ((βs.update i b).headInfo s)) := by sorry

end IncentivesInTeams.Conglomerate
