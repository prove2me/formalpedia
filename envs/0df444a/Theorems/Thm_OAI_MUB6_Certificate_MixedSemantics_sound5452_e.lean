-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5452_e
-- name    : OAI.MUB6.Certificate.MixedSemantics.sound5452_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T17:18:19.140647+00:00
-- url     : https://prove2.me/theorems/ca696bde-05ef-43a9-9a8c-65dc33178e0f
-- title:
--   OAI.MUB6.Certificate.MixedSemantics.sound5452_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedSemantics.sound5452` of [lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound85.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound85.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedSemantics`):
--
--   ```lean
--   theorem sound5452_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
--       (_hF : AllTransitionsFourierZero B) :
--       mixedMoment B node5452 node5452Labels = Sparse.eval nodeValue5452 (mixedVector B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.AllTransitionsFourierZero` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedSemantics.Master` and `OAI.MUB6.Certificate.Sparse.eval` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.mixedMoment` (definitions bundle `OAIQ106E010` of this split); `OAI.MUB6.Certificate.MixedSemantics.node5452` and `OAI.MUB6.Certificate.MixedSemantics.node5452Labels` (definitions bundle `OAIQ106E081` of this split); `OAI.MUB6.Certificate.MixedSemantics.nodeValue5452` (definitions bundle `OAIQ106E084` of this split); `OAI.MUB6.Certificate.MixedSemantics.mixedVector` (definitions bundle `OAIQ106E086` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound578_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound85.lean (declaration OAI.MUB6.Certificate.MixedSemantics.sound5452)

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

theorem sound5452_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5452 node5452Labels = Sparse.eval nodeValue5452 (mixedVector B) := by
  sorry

end MUB6.Certificate.MixedSemantics

end OAI
end
