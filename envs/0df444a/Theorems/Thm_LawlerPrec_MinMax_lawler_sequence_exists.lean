-- Prove2me | Theorems.Thm_LawlerPrec_MinMax_lawler_sequence_exists
-- name    : LawlerPrec.MinMax.lawler_sequence_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:43:43.547122+00:00
-- url     : https://prove2.me/theorems/11f73b22-9713-42b9-b5f6-6c880b95fb8d
-- title:
--   §3 Sequencing Algorithm, p. 545 — the backward rule always produces a complete sequence
-- statement:
--   Let $J$ be a finite set of jobs with arbitrary processing times $a_j$, cost functions $c_j$ and precedence constraints. If some sequence of $J$ observes the precedence constraints, then
--
--   $$
--   \text{some sequence of } J \text{ is produced by Lawler's backward rule.}
--   $$
--
--   In other words, the procedure "one simply finds a job $k$ which can be placed last … and so on" never stalls: at every stage the set of remaining jobs has a job required to precede none of the others, and among those a job of least cost at the remaining total processing time. This ensures that the optimality statement for the rule's sequences is not vacuous.
--
--   **Formalization Note** No assumption on processing times or costs is needed. "Produced by the rule" is the property `IsLawlerSequence` of a finished sequence, with arbitrary tie-breaking.
-- source:
--   Lawler, Optimal Sequencing of a Single Machine Subject to Precedence Constraints, Management Science 19(5), 1973, p. 545, §3 Sequencing Algorithm, first paragraph

import Mathlib
import Definitions.Def_LawlerPrec_MinMax_IsFeasible
import Definitions.Def_LawlerPrec_MinMax_IsLawlerSequence

namespace LawlerPrec.MinMax

/-- §3 Sequencing Algorithm, p. 545, first paragraph: the procedure "one simply finds a job `k`
which can be placed last … and so on" never stalls. If some sequence of `J` observes the
precedence constraints, then some sequence of `J` is produced by the backward rule. No
assumption on processing times or costs is needed. -/
theorem lawler_sequence_exists {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (c : ι → ℝ → ℝ)
    (prec : ι → ι → Prop) (J : Finset ι) (hfeas : ∃ l : List ι, IsFeasible prec J l) :
    ∃ l : List ι, MooreLateJobs.Shared.IsSchedule J l ∧ IsLawlerSequence a c prec l := by sorry

end LawlerPrec.MinMax
