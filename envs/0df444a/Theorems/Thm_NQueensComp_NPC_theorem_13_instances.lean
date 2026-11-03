-- Prove2me | Theorems.Thm_NQueensComp_NPC_theorem_13_instances
-- name    : NQueensComp.NPC.theorem_13_instances
-- status  : Proved
-- author  : @Victorized
-- created : 2026-11-03T02:42:24.581202+00:00
-- url     : https://prove2.me/theorems/4edd4d3a-309e-4fb4-8ae9-b8600c93a26f
-- title:
--   Theorem 13, instance level — Definition 10 preserves validity and the number of solutions
-- statement:
--   Let $\mathrm{def10}$ be the construction of Definition 10, which sends an instance of Problem 3 to an instance of Problem 2 (n-Queens Completion).
--
--   **Claim (instance-level half of Theorem 13, p. 826).** For every valid instance $M_3$ of Problem 3, $\mathrm{def10}(M_3)$ is a valid instance of Problem 2 (n-Queens Completion), and the two instances have the same number of solutions:
--   $$\bigl|\{S : S \text{ solves } \mathrm{def10}(M_3)\}\bigr| = \bigl|\{S : S \text{ solves } M_3\}\bigr|.$$
--
--   The paper proves this through Lemmas 11 and 12, which give solution maps in both directions; the count equality needs in addition that these maps are mutually inverse on solutions. Cardinalities are `Set.ncard` (an infinite set would count as $0$, but both sets here are finite).
--
--   This is one of the two halves of `NQueensComp.NPC.theorem_13`; the other, `theorem_13_codes`, is the statement about bit codes and polynomial-time computability.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from Claude (Anthropic).
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 826, Theorem 13 (instance-level half)

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Theorem 13, instance-level half. -/
theorem theorem_13_instances :
    ∀ M : Inst3, M.Valid →
      (def10 M).Valid ∧
        _root_.Set.ncard {S : Finset Queen | (def10 M).IsSol S} =
          _root_.Set.ncard {S : Finset Queen | M.IsSol S} := by sorry

end NQueensComp.NPC
