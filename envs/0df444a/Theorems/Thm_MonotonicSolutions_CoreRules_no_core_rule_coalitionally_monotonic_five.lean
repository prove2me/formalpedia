-- Prove2me | Theorems.Thm_MonotonicSolutions_CoreRules_no_core_rule_coalitionally_monotonic_five
-- name    : MonotonicSolutions.CoreRules.no_core_rule_coalitionally_monotonic_five
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:00:17.642708+00:00
-- url     : https://prove2.me/theorems/dc6197ee-471f-41e2-a368-14151e72ab4b
-- title:
--   Proof of Theorem 1: the case $|N| = 5$
-- statement:
--   Let $N = \{1, 2, 3, 4, 5\}$. There is no allocation procedure $\varphi$ on five-player games (efficient: $\sum_{i\in N}\varphi_i(v) = v(N)$ for every game $v$ with $v(\emptyset)=0$) that is both
--
--   1. a core allocation rule: $\varphi(v)$ lies in the core of $v$ whenever that core is nonempty, and
--   2. coalitionally monotonic (Eq. (4)): if $v(T) \ge w(T)$ and $v(S) = w(S)$ for all $S \ne T$, then $\varphi_i(v) \ge \varphi_i(w)$ for all $i \in T$.
--
--   This is the five-player case of Theorem 1, which the paper proves directly and then extends to more players.
--
--   **Formalization Note** Games are `Game 5`, the players are `Fin 5`.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 69, proof of Theorem 1 ("no core allocation procedure is monotonic for |N| = 5")

import Mathlib
import Definitions.Def_MonotonicSolutions_CoreRules_Game
import Definitions.Def_MonotonicSolutions_CoreRules_IsCoreRule
import Definitions.Def_MonotonicSolutions_CoreRules_IsCoalitionallyMonotonic

namespace MonotonicSolutions.CoreRules

theorem no_core_rule_coalitionally_monotonic_five :
    ¬ ∃ φ : Game 5 → Fin 5 → ℝ,
      IsAllocationProcedure φ ∧ IsCoreRule φ ∧ IsCoalitionallyMonotonic φ := by sorry

end MonotonicSolutions.CoreRules
