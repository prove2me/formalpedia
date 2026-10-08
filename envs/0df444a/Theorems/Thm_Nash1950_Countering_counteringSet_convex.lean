-- Prove2me | Theorems.Thm_Nash1950_Countering_counteringSet_convex
-- name    : Nash1950.Countering.counteringSet_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:30:44.499893+00:00
-- url     : https://prove2.me/theorems/32ed30e4-a8aa-4395-aee7-43dfe97f1a6b
-- title:
--   Each countering set is convex
-- statement:
--   For any profile $P$ of player strategy vectors, the set $C(P)$ of countering mixed profiles is convex:
--
--   $$
--   Q,R\in C(P),\ 0\le t\le1\quad\Longrightarrow\quad tQ+(1-t)R\in C(P).
--   $$
--
--   Convexity is one of the conditions Nash identifies before applying Kakutani's theorem.
--
--   **Formalization Note.** The claim holds even when $P$ is an arbitrary real weight profile; the source only applies it to a mixed profile.
-- source:
--   Nash, Equilibrium points in n-person games, Proc. Natl. Acad. Sci. USA 36 (1950), p. 49, ¶3, sentence 2 (PDF p. 3)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Nash1950_Countering_Setting

namespace Nash1950.Countering

theorem counteringSet_convex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Type*) [∀ i, Fintype (S i)]
    (u : ι → (∀ i, S i) → ℝ) :
    ∀ P : ∀ i, S i → ℝ, Convex ℝ (counteringSet u P) := by sorry

end Nash1950.Countering
