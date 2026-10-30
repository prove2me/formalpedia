-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram_Rescan_naturalKey_eq_iff
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.naturalKey_eq_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:13:37.582788+00:00
-- url     : https://prove2.me/theorems/cf398e03-b61e-4b5a-830e-c69435b2aeed
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.naturalKey_eq_iff: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.naturalKey_eq_iff` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/AttainedSignatureRescan.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/AttainedSignatureRescan.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan`, with `open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram`):
--
--   ```lean
--   theorem naturalKey_eq_iff {h d : ℕ} (W : List Bool)
--       (c : Fin d → Fin h → List Bool) (A : Fin d → Fin h → ℤ)
--       (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
--         (BinaryArithmetic.toNat W : ℤ) + A j i) (i j : Fin (2 ^ h)) :
--       naturalKey W (List.ofFn (fun row => List.ofFn (c row))) h i =
--         naturalKey W (List.ofFn (fun row => List.ofFn (c row))) h j ↔
--         AttainedSignatures.integerKey A i = AttainedSignatures.integerKey A j
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.integerKey` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.naturalKey` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.scan_kernel` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/AttainedSignatureRescan.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.naturalKey_eq_iff)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S114

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

theorem naturalKey_eq_iff {h d : ℕ} (W : List Bool)
    (c : Fin d → Fin h → List Bool) (A : Fin d → Fin h → ℤ)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) + A j i) (i j : Fin (2 ^ h)) :
    naturalKey W (List.ofFn (fun row => List.ofFn (c row))) h i =
      naturalKey W (List.ofFn (fun row => List.ofFn (c row))) h j ↔
      AttainedSignatures.integerKey A i = AttainedSignatures.integerKey A j := by
  sorry

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end
