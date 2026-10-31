-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQuerySetup_prepare_seed
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.prepare_seed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:09:42.730447+00:00
-- url     : https://prove2.me/theorems/e5e24201-b409-4cc3-a620-6c3403b88011
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.prepare_seed: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.prepare_seed` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQuerySetup.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQuerySetup.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup`, with `open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram`, `open LeafProgram.Query HashGreedyProgram.NativeRound`, `open HighMarkedFrontend`):
--
--   ```lean
--   theorem prepare_seed : ∃ C d : ℕ,
--       ∀ (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
--         (base : Lower) (front : Data) (padding : Fin 8 → ℕ) (w : Bank.Words) (S B : ℕ),
--         FrontState q k base (project front) padding w →
--         (∀ i, ¬H i → (front.stacks i).length ≤ S) →
--         (∀ i, H i → (front.stacks i).length ≤ B) →
--         (∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val i ≤ S) →
--         (∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).len i ≤ S) →
--         front.stacks 728 = [] → Nonempty (PreparedRun q k hg front padding S B (C*(S+1)^d))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank.Words` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.words` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.result` (definitions bundle `OAIQ081S067` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.project` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.code` (definitions bundle `OAIQ081S153` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.Data` (definitions bundle `OAIQ081S173` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.FrontState` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.Lower` (definitions bundle `OAIQ081S176` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.PreparedRun` (definitions bundle `OAIQ081S190` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.accepted` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.marked` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQuerySetup.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.prepare_seed)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S190

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound
open HighMarkedFrontend

local notation "H" => (fun i : Fin 896 => i ∈ HighQueryProgram.Carried.words)

theorem prepare_seed : ∃ C d : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
      (base : Lower) (front : Data) (padding : Fin 8 → ℕ) (w : Bank.Words) (S B : ℕ),
      FrontState q k base (project front) padding w →
      (∀ i, ¬H i → (front.stacks i).length ≤ S) →
      (∀ i, H i → (front.stacks i).length ≤ B) →
      (∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val i ≤ S) →
      (∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).len i ≤ S) →
      front.stacks 728 = [] → Nonempty (PreparedRun q k hg front padding S B (C*(S+1)^d)) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
end
