-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3089_e
-- name    : OAI.MUB6.Certificate.MixedSemantics.sound3089_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T15:31:32.086999+00:00
-- url     : https://prove2.me/theorems/979b2a3c-6dd6-4044-b7df-ae7549d820c1
-- title:
--   OAI.MUB6.Certificate.MixedSemantics.sound3089_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedSemantics.sound3089` of [lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound48.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound48.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedSemantics`):
--
--   ```lean
--   theorem sound3089_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
--       (_hF : AllTransitionsFourierZero B) :
--       mixedMoment B node3089 node3089Labels = Sparse.eval nodeValue3089 (mixedVector B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.AllTransitionsFourierZero` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedSemantics.Master` and `OAI.MUB6.Certificate.Sparse.eval` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.mixedMoment` (definitions bundle `OAIQ106E010` of this split); `OAI.MUB6.Certificate.MixedSemantics.node3089` and `OAI.MUB6.Certificate.MixedSemantics.node3089Labels` (definitions bundle `OAIQ106E079` of this split); `OAI.MUB6.Certificate.MixedSemantics.nodeValue3089` (definitions bundle `OAIQ106E084` of this split); `OAI.MUB6.Certificate.MixedSemantics.mixedVector` (definitions bundle `OAIQ106E086` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound591_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound48.lean (declaration OAI.MUB6.Certificate.MixedSemantics.sound3089)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3089_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3089 node3089Labels = Sparse.eval nodeValue3089 (mixedVector B) := by
  sorry

end MUB6.Certificate.MixedSemantics

end OAI
end
