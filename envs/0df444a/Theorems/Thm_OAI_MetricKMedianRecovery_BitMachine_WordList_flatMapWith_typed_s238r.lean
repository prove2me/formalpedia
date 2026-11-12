-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_WordList_flatMapWith_typed_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.WordList.flatMapWith_typed_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:34:12.634553+00:00
-- url     : https://prove2.me/theorems/c175c2e8-1372-4ce1-9766-cb6d91e26822
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.WordList.flatMapWith_typed_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.WordList.flatMapWith_typed` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/RefineMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/RefineMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.WordList`, with `open WordOperations`):
--
--   ```lean
--   lemma flatMapWith_typed_s238r {A B : Type*} (encA : A → List Bool) (encB : B → List Bool)
--       (f : List Bool → List Bool) (ctx : List Bool) (g : A → List B) (xs : List A)
--       (h : ∀ a∈xs,f (pairBits (ctx,encA a))=encode ((g a).map encB)) :
--       flatMapWith f (pairBits (ctx,encode (xs.map encA)))=encode ((xs.flatMap g).map encB)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238L006` of this split); `OAI.MetricKMedianRecovery.BitMachine.WordList.flatMapWith` (definitions bundle `Q238L015` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/RefineMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.WordList.flatMapWith_typed)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList
open WordOperations
lemma flatMapWith_typed_s238r {A B : Type*} (encA : A → List Bool) (encB : B → List Bool)
    (f : List Bool → List Bool) (ctx : List Bool) (g : A → List B) (xs : List A)
    (h : ∀ a∈xs,f (pairBits (ctx,encA a))=encode ((g a).map encB)) :
    flatMapWith f (pairBits (ctx,encode (xs.map encA)))=encode ((xs.flatMap g).map encB) := by
  sorry
end MetricKMedianRecovery.BitMachine.WordList

end OAI
end
