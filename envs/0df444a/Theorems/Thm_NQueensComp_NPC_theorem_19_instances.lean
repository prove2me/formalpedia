-- Prove2me | Theorems.Thm_NQueensComp_NPC_theorem_19_instances
-- name    : NQueensComp.NPC.theorem_19_instances
-- status  : Proved
-- author  : @Victorized
-- created : 2026-11-03T02:42:30.792547+00:00
-- url     : https://prove2.me/theorems/e23cd4f3-07be-497f-84d7-abb5f1203bd4
-- title:
--   Theorem 19, instance level — Definition 16 preserves validity and the number of solutions
-- statement:
--   Let $\mathrm{def16}$ be the construction of Definition 16, which sends an instance of Problem 4 (Excluded Diagonals) to an instance of Problem 3.
--
--   **Claim (instance-level half of Theorem 19, p. 827).** For every valid instance $M_4$ of Problem 4 (Excluded Diagonals), $\mathrm{def16}(M_4)$ is a valid instance of Problem 3, and the two instances have the same number of solutions:
--   $$\bigl|\{S : S \text{ solves } \mathrm{def16}(M_4)\}\bigr| = \bigl|\{S : S \text{ solves } M_4\}\bigr|.$$
--
--   The paper proves this through Lemmas 17 and 18, which give solution maps in both directions; the count equality needs in addition that these maps are mutually inverse on solutions. Cardinalities are `Set.ncard` (an infinite set would count as $0$, but both sets here are finite).
--
--   This is one of the two halves of `NQueensComp.NPC.theorem_19`; the other, `theorem_19_codes`, is the statement about bit codes and polynomial-time computability.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from Claude (Anthropic).
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 827, Theorem 19 (instance-level half)

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Theorem 19, instance-level half. -/
theorem theorem_19_instances :
    ∀ M : Inst4, M.Valid →
      (def16 M).Valid ∧
        _root_.Set.ncard {S : Finset Queen | (def16 M).IsSol S} =
          _root_.Set.ncard {S : Finset Queen | M.IsSol S} := by sorry

end NQueensComp.NPC
