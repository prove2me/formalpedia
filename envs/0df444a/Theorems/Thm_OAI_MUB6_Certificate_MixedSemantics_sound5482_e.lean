-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5482_e
-- name    : OAI.MUB6.Certificate.MixedSemantics.sound5482_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T17:22:33.708048+00:00
-- url     : https://prove2.me/theorems/0b83f9bf-c501-494e-8e9e-3e5a3d8d7371
-- title:
--   OAI.MUB6.Certificate.MixedSemantics.sound5482_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedSemantics.sound5482` of [lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound85.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound85.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedSemantics`):
--
--   ```lean
--   theorem sound5482_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
--       (_hF : AllTransitionsFourierZero B) :
--       mixedMoment B node5482 node5482Labels = Sparse.eval nodeValue5482 (mixedVector B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.AllTransitionsFourierZero` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedSemantics.Master` and `OAI.MUB6.Certificate.Sparse.eval` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.mixedMoment` (definitions bundle `OAIQ106E010` of this split); `OAI.MUB6.Certificate.MixedSemantics.node5482` and `OAI.MUB6.Certificate.MixedSemantics.node5482Labels` (definitions bundle `OAIQ106E081` of this split); `OAI.MUB6.Certificate.MixedSemantics.nodeValue5482` (definitions bundle `OAIQ106E084` of this split); `OAI.MUB6.Certificate.MixedSemantics.mixedVector` (definitions bundle `OAIQ106E086` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound85.lean (declaration OAI.MUB6.Certificate.MixedSemantics.sound5482)

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

theorem sound5482_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5482 node5482Labels = Sparse.eval nodeValue5482 (mixedVector B) := by
  sorry

end MUB6.Certificate.MixedSemantics

end OAI
end
