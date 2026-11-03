-- Prove2me | Theorems.Thm_NQueensComp_NPC_theorem_36_instances
-- name    : NQueensComp.NPC.theorem_36_instances
-- status  : Proved
-- author  : @Victorized
-- created : 2026-11-03T02:42:27.011784+00:00
-- url     : https://prove2.me/theorems/fa452ebe-9dbe-449f-9190-703cb6b84ede
-- title:
--   Theorem 36, instance level — Definition 31 preserves validity and the number of solutions
-- statement:
--   Let $\mathrm{def31}$ be the construction of Definition 31, which sends an instance of Restricted 1-in-3-SAT (Problem 6) to an instance of Problem 5.
--
--   **Claim (instance-level half of Theorem 36, p. 836).** For every valid instance $M_6$ of Restricted 1-in-3-SAT (Problem 6), $\mathrm{def31}(M_6)$ is a valid instance of Problem 5, and the two instances have the same number of solutions:
--   $$\bigl|\{S : S \text{ solves } \mathrm{def31}(M_6)\}\bigr| = \bigl|\{S : S \text{ solves } M_6\}\bigr|.$$
--
--   The paper proves this through Lemmas 33, 34 and 35, which give solution maps in both directions; the count equality needs in addition that these maps are mutually inverse on solutions. Cardinalities are `Set.ncard` (an infinite set would count as $0$, but both sets here are finite).
--
--   This is one of the two halves of `NQueensComp.NPC.theorem_36`; the other, `theorem_36_codes`, is the statement about bit codes and polynomial-time computability.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from Claude (Anthropic).
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 836, Theorem 36 (instance-level half)

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Theorem 36, instance-level half. -/
theorem theorem_36_instances :
    ∀ cs : Inst6, Inst6Valid cs →
      Inst5Valid (def31 cs) ∧
        _root_.Set.ncard {Ss : List (Finset Queen) | Inst5IsSol (def31 cs) Ss} =
          _root_.Set.ncard {T : Finset ℕ | Inst6IsSol cs T} := by sorry

end NQueensComp.NPC
