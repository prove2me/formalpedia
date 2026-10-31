-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation_prepared_words
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepared_words
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:34:56.461956+00:00
-- url     : https://prove2.me/theorems/f5bab2e5-aa5d-42b3-a787-844dbbd5198c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepared_words: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepared_words` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeEvaluation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeEvaluation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation`, with `open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage`, `open LeafHeadSetupProgram QueryTupleState`):
--
--   ```lean
--   theorem prepared_words (s : Native.Inputs) (a : Data)
--       (bits : List Bool) (tail : List (List Bool))
--       (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) (b : Data)
--       (hf : ∀ i, i ∉ PairNativeSetup.scratch → i ≠ 832 → i ≠ 833 → i ≠ 834 → i ≠ 835 →
--         b.stacks i=(bootstrapped s (loadedNode a bits tail) ra rd rc words).stacks i) :
--       b.stacks 78=bits ∧ b.stacks 301=Encoding.encodeList id tail ∧
--         (∀ i ∈ framePorts,b.stacks i=a.stacks i) ∧
--         b.stacks 710=(LayoutProgramScalar.FromCounts.unsignedSaved words s.width s.power s.R s.height).hp ∧
--         b.stacks 711=(LayoutProgramScalar.FromCounts.unsignedSaved words s.width s.power s.R s.height).hn ∧
--         b.stacks 712=s.power.1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup.scratch` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.framePorts` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.Saved` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.unsignedSaved` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.power` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.Data` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.bootstrapped` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.loadedNode` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_native_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeEvaluation.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepared_words)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram QueryTupleState

theorem prepared_words (s : Native.Inputs) (a : Data)
    (bits : List Bool) (tail : List (List Bool))
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) (b : Data)
    (hf : ∀ i, i ∉ PairNativeSetup.scratch → i ≠ 832 → i ≠ 833 → i ≠ 834 → i ≠ 835 →
      b.stacks i=(bootstrapped s (loadedNode a bits tail) ra rd rc words).stacks i) :
    b.stacks 78=bits ∧ b.stacks 301=Encoding.encodeList id tail ∧
      (∀ i ∈ framePorts,b.stacks i=a.stacks i) ∧
      b.stacks 710=(LayoutProgramScalar.FromCounts.unsignedSaved words s.width s.power s.R s.height).hp ∧
      b.stacks 711=(LayoutProgramScalar.FromCounts.unsignedSaved words s.width s.power s.R s.height).hn ∧
      b.stacks 712=s.power.1 := by
  sorry

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end
