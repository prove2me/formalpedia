-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyCode_history_raw_slots
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.history_raw_slots
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:17:37.798913+00:00
-- url     : https://prove2.me/theorems/e8c9f275-53a1-4248-b33b-b9052e3ecd7b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.history_raw_slots: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.history_raw_slots` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCode.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCode.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode`, with `open SqrtLog`, `open scoped BigOperators`, `open HashGreedyCNF`):
--
--   ```lean
--   theorem history_raw_slots {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
--       (hm : 0 < m) (depth : ℕ) (start : List (List Bool)) (rounds : ℕ) :
--       LeafScopeResourceBounds.slots ((history clauses depth start rounds).map (raw m hm)) =
--         LeafScopeResourceBounds.slots (start.map (raw m hm)) + rounds * depth
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.slots` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.raw` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Clause` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_history_raw_resources` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_raw_resources` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCode.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.history_raw_slots)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode

open SqrtLog
open scoped BigOperators
open HashGreedyCNF

noncomputable section

theorem history_raw_slots {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth : ℕ) (start : List (List Bool)) (rounds : ℕ) :
    LeafScopeResourceBounds.slots ((history clauses depth start rounds).map (raw m hm)) =
      LeafScopeResourceBounds.slots (start.map (raw m hm)) + rounds * depth := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode
end
