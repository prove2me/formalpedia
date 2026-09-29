-- Prove2me | Theorems.Thm_JohnsonApprox_MaxSatWeighted_exampleK3_spec
-- name    : JohnsonApprox.MaxSatWeighted.exampleK3_spec
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:36:39.827844+00:00
-- url     : https://prove2.me/theorems/a0d529ea-9dde-4771-85a3-11fcaf764b27
-- title:
--   Proof of Theorem 3 — the k = 3 example: S* = 8 and B2 can return 7 clauses
-- statement:
--   Let $S$ be the eight-clause input
--   $$S = \{\{x_1, x_2, x_3\}, \{\bar x_1, x_4, x_5\}, \{x_1, \bar x_2, x_3\}, \{\bar x_1, x_6, x_7\}, \{x_1, x_2, \bar x_3\}, \{\bar x_1, x_8, x_9\}, \{x_1, \bar x_2, \bar x_3\}, \{\bar x_1, x_{10}, x_{11}\}\}.$$
--   Then:
--
--   1. every clause of $S$ has three distinct literals, so $S$ is an input of MS(3);
--   2. $S^* = 8$;
--   3. algorithm B2 has a choosable output $\mathrm{SUB}$ with $|\mathrm{SUB}| = 7$.
--
--   Hence $r(B2, S) = 8/7 = 2^3/(2^3 - 1)$, showing the bound of Theorem 3 is attained at $k = 3$.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 264, proof of Theorem 3

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatWeighted_B2
import Definitions.Def_JohnsonApprox_MaxSatWeighted_ExampleK3

namespace JohnsonApprox.MaxSatWeighted

/-- Proof of Theorem 3 (p. 264), the lower-bound input for `k = 3`: it is an input of `MS(3)`,
`S* = 8`, and B2 has a choosable output with `7` clauses, so `r(B2, S) = 8/7`. -/
theorem exampleK3_spec :
    Shared.InMS 3 exampleK3 ∧ Shared.opt exampleK3 = 8 ∧ ∃ X, Choosable exampleK3 X ∧ X.card = 7 := by sorry

end JohnsonApprox.MaxSatWeighted
