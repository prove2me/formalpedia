-- Prove2me | Theorems.Thm_IncentivesInTeams_Conglomerate_appendix_lemma
-- name    : IncentivesInTeams.Conglomerate.appendix_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:22:27.125175+00:00
-- url     : https://prove2.me/theorems/7a7ade07-b4b9-4ac6-95bc-d3f47bd38a88
-- title:
--   Appendix LEMMA: the projections of $A(s)$ and $B(s)$ onto $S_j$ agree for $j \ne i$
-- statement:
--   Fix a conglomerate model, a joint strategy $\beta^*$, a subunit $i$ and a strategy $\beta_i \in B_i$. Write $\hat y_0(s)$ for the head's information when $\beta^*/\beta_i$ is played and $y_0^*(s)$ for his information when $\beta^*$ is played. For a state $s$ define (A.3)
--   $$A(s) = \{s' \in S \mid \hat y_0(s') = \hat y_0(s)\}, \qquad B(s) = \{s' \in S \mid y_0^*(s') = \hat y_0(s)\},$$
--   and let $A_j(s)$, $B_j(s)$ be their projections onto the component state space $S_j$. If $B(s)$ is nonempty, then
--   $$A_0(s) = B_0(s) \quad\text{and}\quad A_j(s) = B_j(s) \ \text{ for every subunit } j \ne i.$$
--
--   The lemma says that, for every component other than the deviating subunit, the head's information under the deviation and under $\beta^*$ restricts that component's state in the same way. It is the device by which the paper compares the two sides of (A.2).
--
--   **Formalization Note.** The hypothesis that $B(s)$ is nonempty is added. The paper states the lemma for all $s$, but its proof reads $B_j(s)$ off the single-coordinate condition (A.4), which presumes $B(s) \ne \emptyset$. Without it the statement is false: if $\beta_i$ sends a message that $\gamma_i^*$ never sends, $B(s) = \emptyset$ while $s_j \in A_j(s)$. The hypothesis $\beta_i \in B_i$ is kept as in the paper's setting. The one-exchange protocol of the model file is used for the information functions.
-- source:
--   Groves, Incentives in Teams, Econometrica 41(4), 1973, p. 630, Appendix, (A.3) and LEMMA

import Mathlib
import Definitions.Def_IncentivesInTeams_Conglomerate_Model

namespace IncentivesInTeams.Conglomerate

theorem appendix_lemma {ι : Type*} [Fintype ι] [DecidableEq ι] {S₀ : Type*} [Fintype S₀] {S : ι → Type*}
    [∀ i, Fintype (S i)] {Z₀ : Type*} {Z M₀ M : ι → Type*} {D₀ : Type*} {D : ι → Type*}
    (T : Model S₀ S Z₀ Z M₀ M D₀ D)
    (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (i : ι)
    (b : SubStrategy (S i) (Z i) (M₀ i) (M i) (D i)) (hb : b ∈ T.B i) (s : S₀ × ∀ k, S k)
    (hB : {s' | βs.headInfo s' = (βs.update i b).headInfo s}.Nonempty) :
    Prod.fst '' {s' | (βs.update i b).headInfo s' = (βs.update i b).headInfo s} =
        Prod.fst '' {s' | βs.headInfo s' = (βs.update i b).headInfo s} ∧
      ∀ j, j ≠ i →
        (fun s' : S₀ × ∀ k, S k => s'.2 j) ''
            {s' | (βs.update i b).headInfo s' = (βs.update i b).headInfo s} =
          (fun s' : S₀ × ∀ k, S k => s'.2 j) ''
            {s' | βs.headInfo s' = (βs.update i b).headInfo s} := by sorry

end IncentivesInTeams.Conglomerate
