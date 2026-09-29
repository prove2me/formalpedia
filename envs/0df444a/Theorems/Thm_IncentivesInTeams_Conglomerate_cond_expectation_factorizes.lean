-- Prove2me | Theorems.Thm_IncentivesInTeams_Conglomerate_cond_expectation_factorizes
-- name    : IncentivesInTeams.Conglomerate.cond_expectation_factorizes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:23:06.363715+00:00
-- url     : https://prove2.me/theorems/f393ee08-d245-4623-8e47-5daf57f14d4d
-- title:
--   r.h.s. of (A.2): the head's conditional expectation under $\beta^*$ factorizes over the independent components
-- statement:
--   Consider a conglomerate model whose component weights are probability weights, a joint strategy $\beta^*$ and a value $y_0 = (z_0, m)$ of the head's information. Suppose the event $\{s : y_0^*(s) = y_0\}$ has positive probability under the product law, where $y_0^*$ is the head's information under $\beta^*$. Then for every subunit $j$
--   $$E\big[v_j[\delta_j^*(y_j^*(s)), \delta_0^*(y_0^*(s)); s_j] \,\big|\, y_0^*(s) = y_0\big] = h_j(y_0),$$
--   and for the head's component
--   $$E\big[v_0[\delta_0^*(y_0^*(s)), s_0] \,\big|\, y_0^*(s) = y_0\big] = h_0(y_0),$$
--   where the left-hand sides are the conditional expectations of (3.3) (elementary conditional averages under the product law) and $h_j$, $h_0$ are the factors of $C_i^{II}$ defined in the model file: $h_j$ conditions only subunit $j$'s state on its own message $m_j$, and $h_0$ conditions only the head's state on $\zeta_0^*(s_0) = z_0$.
--
--   This is the formal content of the paper's chain for the right-hand side of (A.2), whose last step "follows by the independence of the distributions of $s_k$ and $s_j$, $k \ne j$". It shows that the factorized compensation $C_i^{II}$ of the mission equals the paper's (3.3) wherever (3.3) is defined.
--
--   **Formalization Note.** Positive probability of the conditioning event is the condition under which the elementary conditional expectation of (3.3) is defined; on a null event the Lean quotient is $0$ and the identity is not claimed. The head's component is included as the paper's bracket "[the proof for $j = 0$ is strictly analogous]" indicates.
-- source:
--   Groves, Incentives in Teams, Econometrica 41(4), 1973, p. 630, Appendix, proof of THEOREM 1, the r.h.s. (A.2) chain (with (3.3), p. 624)

import Mathlib
import Definitions.Def_IncentivesInTeams_Conglomerate_Model

namespace IncentivesInTeams.Conglomerate

theorem cond_expectation_factorizes {ι : Type*} [Fintype ι] [DecidableEq ι] {S₀ : Type*} [Fintype S₀] {S : ι → Type*}
    [∀ i, Fintype (S i)] {Z₀ : Type*} {Z M₀ M : ι → Type*} {D₀ : Type*} {D : ι → Type*}
    (T : Model S₀ S Z₀ Z M₀ M D₀ D) (hT : T.WeightsOK)
    (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (y₀ : Z₀ × ∀ k, M k)
    (hpos : 0 < T.expect (Set.indicator {s | βs.headInfo s = y₀} (fun _ => (1 : ℝ)))) :
    (∀ j, T.literalSubCondExp βs j y₀ = T.subFactor βs j y₀) ∧
      T.literalHeadCondExp βs y₀ = T.headFactor βs y₀ := by sorry

end IncentivesInTeams.Conglomerate
