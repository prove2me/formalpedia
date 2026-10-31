-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashQueryParameterBounds_accepted_envelope
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_envelope
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:10:47.96318+00:00
-- url     : https://prove2.me/theorems/e68de096-c74c-4484-8ceb-a9193a6a8599
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_envelope: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_envelope` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashQueryParameterBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashQueryParameterBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds`, with `open BitProgram StructuredCalls SqrtLog DisjointReuse HighFrontendSources`, `open HashGreedyCode HashQueryEntry ProducedQueryResources`, `open CostAssembly MulticolorTypes`):
--
--   ```lean
--   theorem accepted_envelope (k C d e power ordinaryPower : ℕ) (hk : 2 ≤ k) :
--       ∃ cutoff : ℕ, ∀ n ≥ cutoff,
--         let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
--         ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
--           F.length ≤ n * B →
--         ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
--           (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
--         ∀ (state : State 40 896),
--           (state.stacks 783).length = HashCandidates.digitWidth F.length →
--           BinaryArithmetic.toNat (state.stacks 782) = F.length →
--           BinaryArithmetic.toNat (state.stacks 785) = n →
--         let q := acceptedQuery F hm shifts Q rounds state
--         q.Valid ∧ ambient q = n ∧ ScanBounds q k (4 * k + 3) ∧ SmallInputs q k n ∧
--           ∀ (hg : LeafParametersProgram.Guard (q.input k))
--             (a : Word (problem q k hg).r (problem q k hg).Q)
--             (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
--             (a :: tail).Nodup → (∀ z, z ∈ a :: tail) →
--             let p := ofPacking q k B C d (2 * (k - 1) + 1) e hg a tail
--             Bounds (2 * (k - 1) + 1) (4 * k + 3) (9 * e + 8) n p ∧
--             (nativeEnvelope k n power ordinaryPower p : ℝ) ≤
--               (18 : ℝ) ^ power * (2 : ℝ) ^
--                 ((1 + (power : ℝ) * exponentConstant k (4 * k + 3)) * Statement.runtimeScale n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause` and `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Resources` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.exponentConstant` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Bounds` (definitions bundle `OAIQ081S029` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.nativeEnvelope` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.digitWidth` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Valid` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ambient` (definitions bundle `OAIQ081S171` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.acceptedQuery` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ScanBounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.SmallInputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ofPacking` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.problem` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.SAT.Literal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeScale` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashQueryParameterBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_envelope)

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

open CostAssembly MulticolorTypes

theorem accepted_envelope (k C d e power ordinaryPower : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∀ n ≥ cutoff,
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
        F.length ≤ n * B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (state : State 40 896),
        (state.stacks 783).length = HashCandidates.digitWidth F.length →
        BinaryArithmetic.toNat (state.stacks 782) = F.length →
        BinaryArithmetic.toNat (state.stacks 785) = n →
      let q := acceptedQuery F hm shifts Q rounds state
      q.Valid ∧ ambient q = n ∧ ScanBounds q k (4 * k + 3) ∧ SmallInputs q k n ∧
        ∀ (hg : LeafParametersProgram.Guard (q.input k))
          (a : Word (problem q k hg).r (problem q k hg).Q)
          (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
          (a :: tail).Nodup → (∀ z, z ∈ a :: tail) →
          let p := ofPacking q k B C d (2 * (k - 1) + 1) e hg a tail
          Bounds (2 * (k - 1) + 1) (4 * k + 3) (9 * e + 8) n p ∧
          (nativeEnvelope k n power ordinaryPower p : ℝ) ≤
            (18 : ℝ) ^ power * (2 : ℝ) ^
              ((1 + (power : ℝ) * exponentConstant k (4 * k + 3)) * Statement.runtimeScale n) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds
end
