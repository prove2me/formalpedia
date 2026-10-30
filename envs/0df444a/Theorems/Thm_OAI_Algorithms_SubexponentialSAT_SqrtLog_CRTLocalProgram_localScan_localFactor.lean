-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_localScan_localFactor
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localScan_localFactor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:36:06.02551+00:00
-- url     : https://prove2.me/theorems/6de0c4b0-fced-416b-bf04-4b87146fba14
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localScan_localFactor: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localScan_localFactor` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramScanAlgebra.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramScanAlgebra.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram`, with `open Polynomial`, `open scoped BigOperators`):
--
--   ```lean
--   theorem localScan_localFactor {Q : ℕ} (nodes : Fin Q → CodeC) (i : Fin Q)
--       (skip : List Bool) (hskip : skip.length = i.val) (one : S)
--       (hone : denote one = Truncation.trunc J 1) :
--       denote (SubexpNodeScanControl.run (localUpdate cm ca pm linear (nodes i) minusOne J)
--         (List.ofFn nodes) ⟨one,skip,true⟩).value =
--         Truncation.trunc J (TruncatedInverse.localFactor (fun j => decode (nodes j)) J i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Truncation.trunc` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.run` and `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.Cursor` (definitions bundle `OAIQ081S022` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localUpdate` (definitions bundle `OAIQ081S028` of this split); `OAI.Algorithms.SubexponentialSAT.TruncatedInverse.localFactor` (definitions bundle `OAIQ081S042` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.corrected_denote` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramScanAlgebra.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localScan_localFactor)

import Mathlib
import Definitions.Def_OAIQ081S022
import Definitions.Def_OAIQ081S028
import Definitions.Def_OAIQ081S042

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open Polynomial
open scoped BigOperators

section
variable {CodeC S R : Type*} [CommRing R]
variable (decode : CodeC → R) (denote : S → R[X]) (cm ca : CodeC → CodeC → CodeC) (pm : S → S → S)
variable (hm : ∀ a b, decode (cm a b) = decode a * decode b)
variable (ha : ∀ a b, decode (ca a b) = decode a + decode b)
variable (J : ℕ) (linear : CodeC → S)
variable (hp : ∀ a b, denote (pm a b) = Truncation.trunc J (denote a * denote b))
variable (hl : ∀ a, denote (linear a) = Truncation.trunc J (X + C (decode a)))
variable (theta minusOne : CodeC) (hn : decode minusOne = -1)
include hm ha hp hl hn

theorem localScan_localFactor {Q : ℕ} (nodes : Fin Q → CodeC) (i : Fin Q)
    (skip : List Bool) (hskip : skip.length = i.val) (one : S)
    (hone : denote one = Truncation.trunc J 1) :
    denote (SubexpNodeScanControl.run (localUpdate cm ca pm linear (nodes i) minusOne J)
      (List.ofFn nodes) ⟨one,skip,true⟩).value =
      Truncation.trunc J (TruncatedInverse.localFactor (fun j => decode (nodes j)) J i) := by
  sorry

end
end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end
