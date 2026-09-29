-- Prove2me | Theorems.Thm_MonotonicSolutions_CoreRules_core_youngV
-- name    : MonotonicSolutions.CoreRules.core_youngV
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:59:43.996057+00:00
-- url     : https://prove2.me/theorems/3025381f-0df7-4a4a-ac2e-74e605648af1
-- title:
--   Proof of Theorem 1: the core of $v$ is $\{(3,0,0,6,3)\}$
-- statement:
--   Let $v$ be the five-player game of the proof of Theorem 1: identical to the game $w$ (defined from $S_1 = \{3,5\}$, $S_2 = \{1,2,3\}$, $S_3 = \{1,3,4\}$, $S_4 = \{2,4,5\}$, $S_5 = \{1,2,4,5\}$ with $w(S_1)=w(S_2)=3$, $w(S_3)=w(S_4)=w(S_5)=9$, $w(N)=11$, and $w(S) = \max_{S_k\subseteq S} w(S_k)$ or $0$ otherwise), except that $v(S_5) = v(N) = 12$.
--
--   Then the core of $v$ consists of exactly one point:
--   $$C(v) = \{\bar{\bar x}\}, \qquad \bar{\bar x} = (3, 0, 0, 6, 3).$$
--
--   Compared with the core point $(0,1,2,7,1)$ of $w$, players 2 and 4 receive less, although every coalition containing them has weakly increased in value.
--
--   **Formalization Note** The core is the published `Supermodularity.Cooperative.Core Finset.univ`; $\bar{\bar x}$ is `![3, 0, 0, 6, 3]` (paper's player $k$ = Lean index $k-1$).
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 69, proof of Theorem 1 (the unique core element of v is (3, 0, 0, 6, 3))

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MonotonicSolutions_CoreRules_Game
import Definitions.Def_MonotonicSolutions_CoreRules_YoungGames

namespace MonotonicSolutions.CoreRules

theorem core_youngV :
    Supermodularity.Cooperative.Core Finset.univ youngV.1 = {![3, 0, 0, 6, 3]} := by sorry

end MonotonicSolutions.CoreRules
