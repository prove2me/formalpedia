-- Prove2me | Theorems.Thm_MonotonicSolutions_CoreRules_no_core_rule_coalitionally_monotonic
-- name    : MonotonicSolutions.CoreRules.no_core_rule_coalitionally_monotonic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:00:47.62877+00:00
-- url     : https://prove2.me/theorems/6a40af54-7564-4b93-a5ff-74ff826c7c5f
-- title:
--   Theorem 1 — for $|N| \ge 5$ no core allocation rule is coalitionally monotonic
-- statement:
--   Let $n \ge 5$ and $N = \{1, \dots, n\}$. A cooperative game on $N$ is a function $v$ on coalitions with $v(\emptyset) = 0$; an allocation procedure $\varphi$ assigns to each game an allocation $\varphi(v)\in\mathbb{R}^N$ with $\sum_{i \in N} \varphi_i(v) = v(N)$. Then there is no allocation procedure $\varphi$ that is simultaneously
--
--   1. a **core allocation rule**: whenever the core
--   $$C(v) = \Big\{x : \sum_{i\in S} x_i \ge v(S) \ \forall S \subseteq N,\ \sum_{i\in N} x_i = v(N)\Big\}$$
--   is nonempty, $\varphi(v) \in C(v)$; and
--   2. **coalitionally monotonic**: for all games $v, w$ and coalitions $T$, if $v(T) \ge w(T)$ and $v(S) = w(S)$ for all $S \ne T$, then $\varphi_i(v) \ge \varphi_i(w)$ for every $i \in T$.
--
--   In words: for five or more players, staying in the core is incompatible with the principle that raising the value of a coalition never hurts its members. Solution concepts that select from the core, such as the nucleolus, must therefore violate coalitional monotonicity.
--
--   **Formalization Note** Players are `Fin n`; games are `Game n`, the subtype of functions vanishing at $\emptyset$. The core is the published `Supermodularity.Cooperative.Core Finset.univ`. Efficiency is part of the hypothesis, as in the paper's definition of an allocation procedure.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 69, Theorem 1

import Mathlib
import Definitions.Def_MonotonicSolutions_CoreRules_Game
import Definitions.Def_MonotonicSolutions_CoreRules_IsCoreRule
import Definitions.Def_MonotonicSolutions_CoreRules_IsCoalitionallyMonotonic

namespace MonotonicSolutions.CoreRules

theorem no_core_rule_coalitionally_monotonic (n : ℕ) (hn : 5 ≤ n) :
    ¬ ∃ φ : Game n → Fin n → ℝ,
      IsAllocationProcedure φ ∧ IsCoreRule φ ∧ IsCoalitionallyMonotonic φ := by sorry

end MonotonicSolutions.CoreRules
