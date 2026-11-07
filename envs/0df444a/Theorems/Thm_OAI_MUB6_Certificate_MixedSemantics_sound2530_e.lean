-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound2530_e
-- name    : OAI.MUB6.Certificate.MixedSemantics.sound2530_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T14:29:46.690204+00:00
-- url     : https://prove2.me/theorems/e9d4a573-8a83-410d-9bf2-873d385bacd9
-- title:
--   OAI.MUB6.Certificate.MixedSemantics.sound2530_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedSemantics.sound2530` of [lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound39.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound39.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedSemantics`):
--
--   ```lean
--   theorem sound2530_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
--       (_hF : AllTransitionsFourierZero B) :
--       mixedMoment B node2530 node2530Labels = Sparse.eval nodeValue2530 (mixedVector B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.AllTransitionsFourierZero` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedSemantics.Master` and `OAI.MUB6.Certificate.Sparse.eval` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.mixedMoment` (definitions bundle `OAIQ106E010` of this split); `OAI.MUB6.Certificate.MixedSemantics.node2530` and `OAI.MUB6.Certificate.MixedSemantics.node2530Labels` (definitions bundle `OAIQ106E079` of this split); `OAI.MUB6.Certificate.MixedSemantics.nodeValue2530` (definitions bundle `OAIQ106E084` of this split); `OAI.MUB6.Certificate.MixedSemantics.mixedVector` (definitions bundle `OAIQ106E086` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound39.lean (declaration OAI.MUB6.Certificate.MixedSemantics.sound2530)

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

theorem sound2530_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2530 node2530Labels = Sparse.eval nodeValue2530 (mixedVector B) := by
  sorry

end MUB6.Certificate.MixedSemantics

end OAI
end
