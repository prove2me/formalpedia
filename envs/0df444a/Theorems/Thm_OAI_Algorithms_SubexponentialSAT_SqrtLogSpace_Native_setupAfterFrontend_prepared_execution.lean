-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_setupAfterFrontend_prepared_execution
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_prepared_execution
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:20:29.255318+00:00
-- url     : https://prove2.me/theorems/0b24d154-4c77-47fc-8d32-40b6507600f5
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_prepared_execution: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_prepared_execution` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativePrepared.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativePrepared.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native`, with `open BitProgram StructuredCalls BinaryArithmetic DisjointReuse`):
--
--   ```lean
--   theorem setupAfterFrontend_prepared_execution (k : ℕ) (hk : 2 ≤ k) :
--       ∃ C : ℕ, 1 ≤ C ∧ ∀ {n : ℕ} (F : SAT.CNF (Fin n))
--         (binary : List Bool) (a : State 80 1220),
--         FrontendReady F binary a → toNat binary = n → binary.length ≤ n →
--         20 ≤ n → 0 < sparsifySchedule n → ∃ steps b,
--           DFSVisit.BoundedEval (setupAfterFrontend k) steps a b
--             ((C + 1220) * (Encoding.formulaBitLength F + 1) ^ 3) ∧
--           DFSStartup.Prepared (b.stacks 259)
--             (ExecCNF.normalize SAT.Literal.negate (ExecQuantitativeSparsify.formulaList F)) b ∧
--           SetupReady k F b ∧ steps + 1 ≤ C * (Encoding.formulaBitLength F + 1) ^ 3
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.normalize` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal.negate` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.ExecQuantitativeSparsify.formulaList` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.FrontendReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.SetupReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSStartup.Prepared`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.BoundedEval` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.Data` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.formulaBitLength`, `OAI.Algorithms.SubexponentialSAT.SAT.CNF` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativePrepared.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_prepared_execution)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic DisjointReuse

theorem setupAfterFrontend_prepared_execution (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {n : ℕ} (F : SAT.CNF (Fin n))
      (binary : List Bool) (a : State 80 1220),
      FrontendReady F binary a → toNat binary = n → binary.length ≤ n →
      20 ≤ n → 0 < sparsifySchedule n → ∃ steps b,
        DFSVisit.BoundedEval (setupAfterFrontend k) steps a b
          ((C + 1220) * (Encoding.formulaBitLength F + 1) ^ 3) ∧
        DFSStartup.Prepared (b.stacks 259)
          (ExecCNF.normalize SAT.Literal.negate (ExecQuantitativeSparsify.formulaList F)) b ∧
        SetupReady k F b ∧ steps + 1 ≤ C * (Encoding.formulaBitLength F + 1) ^ 3 := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end
