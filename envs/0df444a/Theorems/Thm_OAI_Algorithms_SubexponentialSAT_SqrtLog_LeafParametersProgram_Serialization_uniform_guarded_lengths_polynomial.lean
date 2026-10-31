-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafParametersProgram_Serialization_uniform_guarded_lengths_polynomial
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.uniform_guarded_lengths_polynomial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:48:51.48486+00:00
-- url     : https://prove2.me/theorems/24a65732-141b-45ff-9e1b-f6d6f3ea3ca3
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.uniform_guarded_lengths_polynomial: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.uniform_guarded_lengths_polynomial` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramSerializationBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramSerializationBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization`, with `open Circuit`):
--
--   ```lean
--   theorem uniform_guarded_lengths_polynomial :
--       ∃ C d : ℕ, ∀ (x : Input) (l : Fin 8 → ℕ) (S : ℕ),
--         FrontendBounds.CountsBound x S → (∀ i,l i ≤ S) →
--         ∀ j, (result code (Execute.guardedModel x l)).len j ≤ C*(S+1)^d
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Input` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.result` (definitions bundle `OAIQ081S067` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.code` (definitions bundle `OAIQ081S153` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.CountsBound` (definitions bundle `OAIQ081S169` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.accepted_with_shadow` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.marked_with_shadow` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafParametersProgramSerializationBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.uniform_guarded_lengths_polynomial)

import Mathlib
import Definitions.Def_OAIQ081S169

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

open Circuit
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem uniform_guarded_lengths_polynomial :
    ∃ C d : ℕ, ∀ (x : Input) (l : Fin 8 → ℕ) (S : ℕ),
      FrontendBounds.CountsBound x S → (∀ i,l i ≤ S) →
      ∀ j, (result code (Execute.guardedModel x l)).len j ≤ C*(S+1)^d := by
  sorry

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

end OAI.Algorithms
end
