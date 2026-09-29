-- Prove2me | Theorems.Thm_MonotonicSolutions_StrongMono_shapley_isStronglyMonotonic
-- name    : MonotonicSolutions.StrongMono.shapley_isStronglyMonotonic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:05:18.511329+00:00
-- url     : https://prove2.me/theorems/5047a0bc-1b2c-417f-82c5-443033bfb6bf
-- title:
--   The Shapley value is strongly monotonic
-- statement:
--   Let $N = \{1, \dots, n\}$ and let $\mathrm{Sh}$ denote the Shapley value. For all games $v, w$ on $N$ with $v(\emptyset) = w(\emptyset) = 0$ and every player $i$,
--   $$w^i(S) \le v^i(S) \text{ for all } S \subseteq N \quad \Longrightarrow \quad \mathrm{Sh}_i(w) \le \mathrm{Sh}_i(v),$$
--   where $v^i(S)$ is the marginal contribution of $i$ to $S$, Eq. (3).
--
--   The paper opens the proof of Theorem 2 with "It is clear that the Shapley value is strongly monotonic"; together with efficiency and symmetry this is the existence part of the theorem.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 70, proof of Theorem 2 (first sentence)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

/-- Young (1985, p. 70, proof of Theorem 2): "It is clear that the Shapley value is strongly
monotonic." For all games `v, w` and every player `i`, if `w^i(S) ≤ v^i(S)` for every
coalition `S`, then `Sh_i(w) ≤ Sh_i(v)`. -/
theorem shapley_isStronglyMonotonic {n : ℕ} :
    IsStronglyMonotonic (fun v : Game n => Supermodularity.Cooperative.ShapleyValue v.1) := by sorry

end MonotonicSolutions.StrongMono
