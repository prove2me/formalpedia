-- Prove2me | Theorems.Thm_Nash1950_Countering_expectedPayoff_update_linear
-- name    : Nash1950.Countering.expectedPayoff_update_linear
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:08:49.985298+00:00
-- url     : https://prove2.me/theorems/313d795d-e9d6-4b22-93d4-87d995ec9b04
-- title:
--   Expected payoffs are polylinear in the players' strategy vectors
-- statement:
--   Let $U_i(P)$ be player $i$'s expected payoff in a finite game. Holding every strategy except player $j$'s vector fixed, $U_i$ is linear in that vector: for real $a,b$ and real vectors $\tau_j,\tau'_j$,
--
--   $$
--   U_i(a\tau_j+b\tau'_j,P_{-j})=aU_i(\tau_j,P_{-j})+bU_i(\tau'_j,P_{-j}).
--   $$
--
--   This is the polylinearity of the expected payoff functions used in the countering correspondence. The identity extends the payoff polynomial from lotteries to arbitrary real weight vectors, where linear combinations are defined.
--
--   **Formalization Note.** No probability constraint is placed on the weight vectors in this algebraic identity; the source calls the restriction to mixed strategies a polylinear form.
-- source:
--   Nash, Equilibrium points in n-person games, Proc. Natl. Acad. Sci. USA 36 (1950), pp. 48–49, opening paragraph and p. 49 ¶1 (PDF pp. 2–3)

import Mathlib
import Definitions.Def_agt_games

namespace Nash1950.Countering

theorem expectedPayoff_update_linear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Type*) [∀ i, Fintype (S i)]
    (u : ι → (∀ i, S i) → ℝ) :
    ∀ (P : ∀ i, S i → ℝ) (j i : ι) (τ τ' : S j → ℝ) (a b : ℝ),
      AGT.expectedPayoff u (Function.update P j (a • τ + b • τ')) i =
        a * AGT.expectedPayoff u (Function.update P j τ) i +
          b * AGT.expectedPayoff u (Function.update P j τ') i := by sorry

end Nash1950.Countering
