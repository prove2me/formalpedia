-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_canonical_normalized_body_length
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_normalized_body_length
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:51:51.032336+00:00
-- url     : https://prove2.me/theorems/386b1505-cc9b-43db-97d1-de31c9aae098
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_normalized_body_length: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_normalized_body_length` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeDFSIntegration.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeDFSIntegration.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native`, with `open BitProgram StructuredCalls BinaryArithmetic DisjointReuse`):
--
--   ```lean
--   theorem canonical_normalized_body_length {n k : ℕ} (F : SAT.CNF (Fin n))
--       (hw : SAT.WidthAtMost k F) :
--       (SubexpNormalizationCorrectness.normalizedBody F).length ≤
--         SparseCountProgram.formulaBound n k
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.formulaBound` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationCorrectness.normalizedBody` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.CNF` and `OAI.Algorithms.SubexponentialSAT.SAT.WidthAtMost` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeDFSIntegration.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_normalized_body_length)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S064

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic DisjointReuse

theorem canonical_normalized_body_length {n k : ℕ} (F : SAT.CNF (Fin n))
    (hw : SAT.WidthAtMost k F) :
    (SubexpNormalizationCorrectness.normalizedBody F).length ≤
      SparseCountProgram.formulaBound n k := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end
