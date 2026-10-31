-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadLoaderBudgets_leafWork_le
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets.leafWork_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:13:22.085264+00:00
-- url     : https://prove2.me/theorems/0f040e54-6755-456f-9b2d-8aa87abe48ef
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets.leafWork_le: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets.leafWork_le` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadLoaderBudgets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadLoaderBudgets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets`, with `open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage`, `open SqrtLog.LeafHeadSetupProgram`):
--
--   ```lean
--   theorem leafWork_le (s : Native.Inputs) (a : Data) (B A z : ℕ)
--       (ha : Native.Ready s a) (hB : WordBound B a)
--       (hrows : s.rows.length = s.n+s.N) (hz : z ≤ A) :
--       36*A+22*(SignatureHeadLoader.localWork s z A+1)+35 ≤
--         (10000000000000000*sizeCoefficient^8)*(A+B+2)^64
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets.sizeCoefficient` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Ready` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localWork` (definitions bundle `OAIQ081S179` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.load_run_polynomial` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.load_run_polynomial` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadLoaderBudgets.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets.leafWork_le)

import Mathlib
import Definitions.Def_OAIQ081S179

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open SqrtLog.LeafHeadSetupProgram

theorem leafWork_le (s : Native.Inputs) (a : Data) (B A z : ℕ)
    (ha : Native.Ready s a) (hB : WordBound B a)
    (hrows : s.rows.length = s.n+s.N) (hz : z ≤ A) :
    36*A+22*(SignatureHeadLoader.localWork s z A+1)+35 ≤
      (10000000000000000*sizeCoefficient^8)*(A+B+2)^64 := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets
end
