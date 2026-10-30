-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_setupAfterFrontend_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:20:03.440668+00:00
-- url     : https://prove2.me/theorems/7ef01c24-829a-4f68-b730-ea51cfa19722
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeSetupSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeSetupSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native`, with `open BitProgram StructuredCalls BinaryArithmetic`):
--
--   ```lean
--   theorem setupAfterFrontend_eval (k : ℕ) (hk : 2 ≤ k) :
--       ∃ C : ℕ, 1 ≤ C ∧ ∀ {n : ℕ} (F : SAT.CNF (Fin n))
--         (binary : List Bool) (a : State 80 1220),
--         FrontendReady F binary a → toNat binary = n → binary.length ≤ n →
--         20 ≤ n → 0 < sparsifySchedule n → ∃ steps b,
--           Eval (setupAfterFrontend k) steps a b ∧ SetupReady k F b ∧
--           steps + 1 ≤ C * (Encoding.formulaBitLength F + 1) ^ 3
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.FrontendReady` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.SetupReady` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.formulaBitLength` and `OAI.Algorithms.SubexponentialSAT.SAT.CNF` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_prepared_execution` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeSetupSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_eval)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic

theorem setupAfterFrontend_eval (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {n : ℕ} (F : SAT.CNF (Fin n))
      (binary : List Bool) (a : State 80 1220),
      FrontendReady F binary a → toNat binary = n → binary.length ≤ n →
      20 ≤ n → 0 < sparsifySchedule n → ∃ steps b,
        Eval (setupAfterFrontend k) steps a b ∧ SetupReady k F b ∧
        steps + 1 ≤ C * (Encoding.formulaBitLength F + 1) ^ 3 := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end
