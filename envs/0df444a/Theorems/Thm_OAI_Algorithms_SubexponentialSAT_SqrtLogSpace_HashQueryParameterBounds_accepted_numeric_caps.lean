-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashQueryParameterBounds_accepted_numeric_caps
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_numeric_caps
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:12:06.314698+00:00
-- url     : https://prove2.me/theorems/bd294f51-8bfa-4c7d-8bf3-df2547747aa8
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_numeric_caps: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_numeric_caps` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashQueryParameterBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashQueryParameterBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds`, with `open BitProgram StructuredCalls SqrtLog DisjointReuse HighFrontendSources`, `open HashGreedyCode HashQueryEntry ProducedQueryResources`):
--
--   ```lean
--   theorem accepted_numeric_caps (k : ℕ) (hk : 2 ≤ k) :
--       ∃ C degree cutoff : ℕ, ∀ n inputLength : ℕ, cutoff ≤ n → n ≤ inputLength →
--         let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
--         ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
--           F.length ≤ n * B →
--         ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
--           (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
--         ∀ (d : State 40 896),
--           (d.stacks 783).length = HashCandidates.digitWidth F.length →
--           BinaryArithmetic.toNat (d.stacks 782) = F.length →
--           BinaryArithmetic.toNat (d.stacks 785) = n →
--         let q := acceptedQuery F hm shifts Q rounds d
--         let S := C * (inputLength + 1) ^ degree
--         q.Valid ∧ ambient q = n ∧ ScanBounds q k (4 * k + 3) ∧ SmallInputs q k n ∧
--           1 ≤ S ∧ n ^ 2 ≤ S ∧ (q.input k).incidences ≤ S ∧
--           ∀ (padding : Fin 8 → ℕ) (j : Fin 64),
--             (LeafParametersProgram.Circuit.result LeafParametersProgram.Serialization.code
--               (LeafParametersProgram.Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
--             (LeafParametersProgram.Execute.guardedModel (q.input k) padding).val j ≤ S
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Input` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.digitWidth` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Valid` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.result` (definitions bundle `OAIQ081S067` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.code` (definitions bundle `OAIQ081S153` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ambient` (definitions bundle `OAIQ081S171` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.acceptedQuery` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ScanBounds` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.SmallInputs` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.accepted_with_shadow` and `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeQueryInputBounds_accepted_inputs` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashQueryParameterBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_numeric_caps)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds

open BitProgram StructuredCalls SqrtLog DisjointReuse HighFrontendSources
open HashGreedyCode HashQueryEntry ProducedQueryResources

theorem accepted_numeric_caps (k : ℕ) (hk : 2 ≤ k) :
    ∃ C degree cutoff : ℕ, ∀ n inputLength : ℕ, cutoff ≤ n → n ≤ inputLength →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
        F.length ≤ n * B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (d : State 40 896),
        (d.stacks 783).length = HashCandidates.digitWidth F.length →
        BinaryArithmetic.toNat (d.stacks 782) = F.length →
        BinaryArithmetic.toNat (d.stacks 785) = n →
      let q := acceptedQuery F hm shifts Q rounds d
      let S := C * (inputLength + 1) ^ degree
      q.Valid ∧ ambient q = n ∧ ScanBounds q k (4 * k + 3) ∧ SmallInputs q k n ∧
        1 ≤ S ∧ n ^ 2 ≤ S ∧ (q.input k).incidences ≤ S ∧
        ∀ (padding : Fin 8 → ℕ) (j : Fin 64),
          (LeafParametersProgram.Circuit.result LeafParametersProgram.Serialization.code
            (LeafParametersProgram.Execute.guardedModel (q.input k) padding)).val j ≤ S ∧
          (LeafParametersProgram.Execute.guardedModel (q.input k) padding).val j ≤ S := by
  sorry

open CostAssembly MulticolorTypes

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds
end
