-- Prove2me | Theorems.Thm_Nash1950_Countering_expectedPayoff_continuous
-- name    : Nash1950.Countering.expectedPayoff_continuous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:11:49.562518+00:00
-- url     : https://prove2.me/theorems/7610c7fa-4c56-4b83-ac95-fdea6bea92b9
-- title:
--   Expected payoff functions are continuous
-- statement:
--   For every player $i$ in a finite game, the expected payoff function $P\mapsto U_i(P)$ is continuous on the product space of real strategy vectors:
--
--   $$
--   U_i:\prod_j\mathbb R^{S_j}\longrightarrow\mathbb R\quad\text{is continuous}.
--   $$
--
--   This continuity is the analytic property Nash invokes to obtain a closed graph for the countering correspondence.
--
--   **Formalization Note.** The assertion is on the entire finite-dimensional vector space; its restriction to mixed profiles is therefore continuous as well.
-- source:
--   Nash, Equilibrium points in n-person games, Proc. Natl. Acad. Sci. USA 36 (1950), p. 49, ¶3, sentence 3 (PDF p. 3)

import Mathlib
import Definitions.Def_agt_games

namespace Nash1950.Countering

theorem expectedPayoff_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Type*) [∀ i, Fintype (S i)]
    (u : ι → (∀ i, S i) → ℝ) :
    ∀ i, Continuous (fun P : ∀ i, S i → ℝ => AGT.expectedPayoff u P i) := by sorry

end Nash1950.Countering
