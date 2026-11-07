-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5483_e
-- name    : OAI.MUB6.Certificate.MixedSemantics.sound5483_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T17:30:59.774448+00:00
-- url     : https://prove2.me/theorems/f692b2a5-57bb-4aa9-827b-f9d1a19fe6e1
-- title:
--   OAI.MUB6.Certificate.MixedSemantics.sound5483_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedSemantics.sound5483` of [lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound85.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound85.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedSemantics`):
--
--   ```lean
--   theorem sound5483_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
--       (_hF : AllTransitionsFourierZero B) :
--       mixedMoment B node5483 node5483Labels = Sparse.eval nodeValue5483 (mixedVector B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.AllTransitionsFourierZero` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedSemantics.Master` and `OAI.MUB6.Certificate.Sparse.eval` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.mixedMoment` (definitions bundle `OAIQ106E010` of this split); `OAI.MUB6.Certificate.MixedSemantics.node5483` and `OAI.MUB6.Certificate.MixedSemantics.node5483Labels` (definitions bundle `OAIQ106E081` of this split); `OAI.MUB6.Certificate.MixedSemantics.nodeValue5483` (definitions bundle `OAIQ106E084` of this split); `OAI.MUB6.Certificate.MixedSemantics.mixedVector` (definitions bundle `OAIQ106E086` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound85.lean (declaration OAI.MUB6.Certificate.MixedSemantics.sound5483)

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

theorem sound5483_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5483 node5483Labels = Sparse.eval nodeValue5483 (mixedVector B) := by
  sorry

end MUB6.Certificate.MixedSemantics

end OAI
end
