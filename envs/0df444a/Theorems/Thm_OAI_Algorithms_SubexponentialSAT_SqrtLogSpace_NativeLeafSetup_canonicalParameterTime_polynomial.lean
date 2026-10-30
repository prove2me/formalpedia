-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafSetup_canonicalParameterTime_polynomial
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalParameterTime_polynomial
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:00:18.430284+00:00
-- url     : https://prove2.me/theorems/83fd37e6-8f8d-4e79-9590-df634027852a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalParameterTime_polynomial: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalParameterTime_polynomial` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafStartup.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafStartup.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup`, with `open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram`):
--
--   ```lean
--   theorem canonicalParameterTime_polynomial :
--       ∃ C d : ℕ, ∀ n m B W ml Bl, 0 < m → 0 < B →
--         ml ≤ W + canonicalStartTime n m W → Bl ≤ W + canonicalStartTime n m W →
--         W + canonicalStartTime n m W +
--           parameterTime m B (W + canonicalStartTime n m W) ml Bl + 1 ≤
--             C * (n + m + W + 16) ^ d
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalStartTime` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameterTime` (definitions bundle `OAIQ081S172` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.chosen_preparation_time_envelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.prepared_common_bound_polynomial` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.prepared_loaded` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafStartup.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalParameterTime_polynomial)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S172

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram

theorem canonicalParameterTime_polynomial :
    ∃ C d : ℕ, ∀ n m B W ml Bl, 0 < m → 0 < B →
      ml ≤ W + canonicalStartTime n m W → Bl ≤ W + canonicalStartTime n m W →
      W + canonicalStartTime n m W +
        parameterTime m B (W + canonicalStartTime n m W) ml Bl + 1 ≤
          C * (n + m + W + 16) ^ d := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
end
