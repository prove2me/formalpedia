-- Prove2me | Theorems.Thm_Nash1950_Countering_counters_self_iff_isMixedNash
-- name    : Nash1950.Countering.counters_self_iff_isMixedNash
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:31:47.425393+00:00
-- url     : https://prove2.me/theorems/56d97fc6-73da-48e4-aee9-034015c773e1
-- title:
--   Self-countering profiles are mixed Nash equilibria
-- statement:
--   A profile $P$ counters itself exactly when it is a mixed Nash equilibrium:
--
--   $$
--   P\in C(P)\quad\Longleftrightarrow\quad P\text{ is a mixed Nash equilibrium}.
--   $$
--
--   Thus the fixed points of Nash's correspondence are precisely the equilibrium points described in the note.
--
--   **Formalization Note.** The right-hand side uses the published definition `AGT.IsMixedNash`; both sides require $P$ to be a tuple of lotteries.
-- source:
--   Nash, Equilibrium points in n-person games, Proc. Natl. Acad. Sci. USA 36 (1950), p. 49, ¶2, sentences 2–3 (PDF p. 3)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Nash1950_Countering_Setting

namespace Nash1950.Countering

theorem counters_self_iff_isMixedNash {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Type*) [∀ i, Fintype (S i)]
    (u : ι → (∀ i, S i) → ℝ) :
    ∀ P : ∀ i, S i → ℝ, Counters u P P ↔ AGT.IsMixedNash u P := by sorry

end Nash1950.Countering
