-- Prove2me | Theorems.Thm_NQueensComp_NPC_theorem_23_instances
-- name    : NQueensComp.NPC.theorem_23_instances
-- status  : Proved
-- author  : @Victorized
-- created : 2026-11-03T02:42:23.454843+00:00
-- url     : https://prove2.me/theorems/d6235076-bb67-47f9-9d87-bd7525fb1d8a
-- title:
--   Theorem 23, instance level — Definition 20 preserves validity and the number of solutions
-- statement:
--   Let $\mathrm{def20}$ be the construction of Definition 20 (corrected: $D^+$ ends at $2n-2$; the empty family is sent to $\langle 1,\{0\},\{0\},\{\},\{\}\rangle$), which sends an instance of Problem 5 to an instance of Problem 4.
--
--   **Claim (instance-level half of Theorem 23, p. 831).** For every valid instance $M_5$ of Problem 5, $\mathrm{def20}(M_5)$ is a valid instance of Problem 4, and the two instances have the same number of solutions:
--   $$\bigl|\{S : S \text{ solves } \mathrm{def20}(M_5)\}\bigr| = \bigl|\{S : S \text{ solves } M_5\}\bigr|.$$
--
--   The paper proves this through Lemmas 21 and 22, which give solution maps in both directions; the count equality needs in addition that these maps are mutually inverse on solutions. Cardinalities are `Set.ncard` (an infinite set would count as $0$, but both sets here are finite).
--
--   This is one of the two halves of `NQueensComp.NPC.theorem_23`; the other, `theorem_23_codes`, is the statement about bit codes and polynomial-time computability.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from Claude (Anthropic).
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 831, Theorem 23 (instance-level half)

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Theorem 23, instance-level half. -/
theorem theorem_23_instances :
    ∀ Ms : Inst5, Inst5Valid Ms →
      (def20 Ms).Valid ∧
        _root_.Set.ncard {S : Finset Queen | (def20 Ms).IsSol S} =
          _root_.Set.ncard {Ss : List (Finset Queen) | Inst5IsSol Ms Ss} := by sorry

end NQueensComp.NPC
