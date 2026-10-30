-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyCNF_history_mass_zero
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history_mass_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:16:18.19288+00:00
-- url     : https://prove2.me/theorems/ec56561e-1ae0-4859-a98c-99aedf0e4581
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history_mass_zero: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history_mass_zero` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCNF.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCNF.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF`, with `open SqrtLog`, `open scoped BigOperators`):
--
--   ```lean
--   theorem history_mass_zero {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
--       (hm : 0 < m) (depth : ℕ) (initial : List (List Bool))
--       (hcode : ∀ v : HashSelect.Row m,
--         (∀ r ∈ initial.map (decode m), (∑ e, r e * v e) = 0) → v ≠ 0 →
--           m ≤ depth * SparseCode.weight v) :
--       HashSelect.mass (rowAccept clauses) (HashInput.violationWeight clauses)
--         (history clauses depth initial (HashSelect.loopCap n m)) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.weight` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.Row` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.mass` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInput.violationWeight` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.decode` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.rowAccept` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Assignment` and `OAI.Algorithms.SubexponentialSAT.SAT.Clause` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics.history_count` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCNF.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history_mass_zero)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF

open SqrtLog
open scoped BigOperators

noncomputable section

theorem history_mass_zero {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth : ℕ) (initial : List (List Bool))
    (hcode : ∀ v : HashSelect.Row m,
      (∀ r ∈ initial.map (decode m), (∑ e, r e * v e) = 0) → v ≠ 0 →
        m ≤ depth * SparseCode.weight v) :
    HashSelect.mass (rowAccept clauses) (HashInput.violationWeight clauses)
      (history clauses depth initial (HashSelect.loopCap n m)) = 0 := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF
end
