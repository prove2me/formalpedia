-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3853_e
-- name    : OAI.MUB6.Certificate.MixedSemantics.sound3853_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T16:17:59.262751+00:00
-- url     : https://prove2.me/theorems/dd50a6a4-c24a-455a-935d-f42ba6adf1d1
-- title:
--   OAI.MUB6.Certificate.MixedSemantics.sound3853_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedSemantics.sound3853` of [lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound60.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound60.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedSemantics`):
--
--   ```lean
--   theorem sound3853_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
--       (_hF : AllTransitionsFourierZero B) :
--       mixedMoment B node3853 node3853Labels = Sparse.eval nodeValue3853 (mixedVector B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.AllTransitionsFourierZero` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedSemantics.Master` and `OAI.MUB6.Certificate.Sparse.eval` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.mixedMoment` (definitions bundle `OAIQ106E010` of this split); `OAI.MUB6.Certificate.MixedSemantics.node3853` and `OAI.MUB6.Certificate.MixedSemantics.node3853Labels` (definitions bundle `OAIQ106E079` of this split); `OAI.MUB6.Certificate.MixedSemantics.nodeValue3853` (definitions bundle `OAIQ106E084` of this split); `OAI.MUB6.Certificate.MixedSemantics.mixedVector` (definitions bundle `OAIQ106E086` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.MixedSemantics.sound5435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound607_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound608_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound60.lean (declaration OAI.MUB6.Certificate.MixedSemantics.sound3853)

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

theorem sound3853_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3853 node3853Labels = Sparse.eval nodeValue3853 (mixedVector B) := by
  sorry

end MUB6.Certificate.MixedSemantics

end OAI
end
