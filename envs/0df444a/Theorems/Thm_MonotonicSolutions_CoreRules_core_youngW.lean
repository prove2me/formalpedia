-- Prove2me | Theorems.Thm_MonotonicSolutions_CoreRules_core_youngW
-- name    : MonotonicSolutions.CoreRules.core_youngW
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:59:19.211959+00:00
-- url     : https://prove2.me/theorems/75997ba5-072a-4b9d-a00f-7419978056a4
-- title:
--   Proof of Theorem 1: the core of $w$ is $\{(0,1,2,7,1)\}$
-- statement:
--   Let $w$ be the five-player game of the proof of Theorem 1: with $S_1 = \{3,5\}$, $S_2 = \{1,2,3\}$, $S_3 = \{1,3,4\}$, $S_4 = \{2,4,5\}$, $S_5 = \{1,2,4,5\}$,
--   $w(S_1) = w(S_2) = 3$, $w(S_3) = w(S_4) = w(S_5) = 9$, $w(N) = 11$, and $w(S) = \max_{S_k \subseteq S} w(S_k)$ (or $0$ if $S$ contains no $S_k$) otherwise.
--
--   Then the core of $w$, the set of $x \in \mathbb{R}^5$ with $\sum_{i \in S} x_i \ge w(S)$ for all $S$ and $\sum_{i \in N} x_i = w(N)$, consists of exactly one point:
--   $$C(w) = \{\bar x\}, \qquad \bar x = (0, 1, 2, 7, 1).$$
--
--   **Formalization Note** The core is the published `Supermodularity.Cooperative.Core Finset.univ`, and the paper's player $k$ is the Lean index $k-1$, so $\bar x$ is `![0, 1, 2, 7, 1]` in the same order.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 69, proof of Theorem 1 (the core of w is x̄ = (0, 1, 2, 7, 1))

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MonotonicSolutions_CoreRules_Game
import Definitions.Def_MonotonicSolutions_CoreRules_YoungGames

namespace MonotonicSolutions.CoreRules

theorem core_youngW :
    Supermodularity.Cooperative.Core Finset.univ youngW.1 = {![0, 1, 2, 7, 1]} := by sorry

end MonotonicSolutions.CoreRules
