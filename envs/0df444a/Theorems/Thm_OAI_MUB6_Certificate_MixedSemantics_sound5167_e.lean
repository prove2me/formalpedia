-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5167_e
-- name    : OAI.MUB6.Certificate.MixedSemantics.sound5167_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T17:03:36.203299+00:00
-- url     : https://prove2.me/theorems/87a1a87d-7322-48c6-91d2-a2fded8a0bc8
-- title:
--   OAI.MUB6.Certificate.MixedSemantics.sound5167_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedSemantics.sound5167` of [lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound80.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound80.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedSemantics`):
--
--   ```lean
--   theorem sound5167_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
--       (_hF : AllTransitionsFourierZero B) :
--       mixedMoment B node5167 node5167Labels = Sparse.eval nodeValue5167 (mixedVector B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.AllTransitionsFourierZero` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedSemantics.Master` and `OAI.MUB6.Certificate.Sparse.eval` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.mixedMoment` (definitions bundle `OAIQ106E010` of this split); `OAI.MUB6.Certificate.MixedSemantics.node5167` and `OAI.MUB6.Certificate.MixedSemantics.node5167Labels` (definitions bundle `OAIQ106E081` of this split); `OAI.MUB6.Certificate.MixedSemantics.nodeValue5167` (definitions bundle `OAIQ106E084` of this split); `OAI.MUB6.Certificate.MixedSemantics.mixedVector` (definitions bundle `OAIQ106E086` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound80.lean (declaration OAI.MUB6.Certificate.MixedSemantics.sound5167)

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

theorem sound5167_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5167 node5167Labels = Sparse.eval nodeValue5167 (mixedVector B) := by
  sorry

end MUB6.Certificate.MixedSemantics

end OAI
end
