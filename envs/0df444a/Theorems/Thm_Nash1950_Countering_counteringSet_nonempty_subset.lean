-- Prove2me | Theorems.Thm_Nash1950_Countering_counteringSet_nonempty_subset
-- name    : Nash1950.Countering.counteringSet_nonempty_subset
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:30:53.259654+00:00
-- url     : https://prove2.me/theorems/c1d8c5d5-9f26-456c-97cd-a609b7a4df04
-- title:
--   The countering correspondence has nonempty values in the mixed-profile space
-- statement:
--   Suppose every player has a finite, nonempty pure-strategy set. For each mixed profile $P$, the set $C(P)$ of profiles countering $P$ is nonempty and consists entirely of mixed profiles:
--
--   $$
--   P\in\Sigma\quad\Longrightarrow\quad C(P)\ne\varnothing\ \text{and}\ C(P)\subseteq\Sigma.
--   $$
--
--   This makes $C$ a correspondence from the product of mixed-strategy spaces into itself, as required for Nash's fixed-point argument.
--
--   **Formalization Note.** Nonemptiness of each pure-strategy set is implicit in the source's use of probability distributions and is explicit here. The player type itself may be empty.
-- source:
--   Nash, Equilibrium points in n-person games, Proc. Natl. Acad. Sci. USA 36 (1950), p. 49, ¶3, sentence 1 (PDF p. 3)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Nash1950_Countering_Setting

namespace Nash1950.Countering

theorem counteringSet_nonempty_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Type*) [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) :
    ∀ P : ∀ i, S i → ℝ, AGT.IsMixedProfile P →
      (counteringSet u P).Nonempty ∧
        counteringSet u P ⊆ {Q | AGT.IsMixedProfile Q} := by sorry

end Nash1950.Countering
