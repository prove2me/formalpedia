-- Prove2me | Theorems.Thm_JohnsonApprox_MaxSatGreedy_exampleK3_spec
-- name    : JohnsonApprox.MaxSatGreedy.exampleK3_spec
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:23:51.503109+00:00
-- url     : https://prove2.me/theorems/b9dfd662-aaea-41a2-b7f0-93095e0d179d
-- title:
--   Proof of Theorem 2: on the k = 3 example, S* = 4 and B1(S) = 3
-- statement:
--   Let $S = \{\{x_1, x_2, x_3\}, \{\bar x_1, x_4, x_5\}, \{\bar x_2, x_6, x_7\}, \{\bar x_3, x_8, x_9\}\}$ be the input of p. 263. Then
--
--   1. $S$ is an input of $MS(3)$: every clause has three distinct literals;
--   2. $S^* = 4$;
--   3. some set $X$ of clauses choosable by B1 on $S$ has $|X| = 3$;
--   4. every set $X$ choosable by B1 on $S$ has $|X| \ge 3$.
--
--   Parts 3 and 4 together say $B1(S) = 3$, the minimum of $|X|$ over choosable outputs. Hence the ratio of B1 on $S$ is $4/3 = (k+1)/k$ for $k = 3$, the tightness example the paper gives for Theorem 2.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 263, proof of Theorem 2

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatGreedy_B1
import Definitions.Def_JohnsonApprox_MaxSatGreedy_ExampleK3

namespace JohnsonApprox.MaxSatGreedy

theorem exampleK3_spec :
    Shared.InMS 3 exampleK3 ∧ Shared.opt exampleK3 = 4 ∧
      (∃ X, Choosable exampleK3 X ∧ X.card = 3) ∧ (∀ X, Choosable exampleK3 X → 3 ≤ X.card) := by sorry

end JohnsonApprox.MaxSatGreedy
