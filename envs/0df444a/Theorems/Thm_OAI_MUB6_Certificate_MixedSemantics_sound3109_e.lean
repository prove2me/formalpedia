-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3109_e
-- name    : OAI.MUB6.Certificate.MixedSemantics.sound3109_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T15:37:32.541914+00:00
-- url     : https://prove2.me/theorems/6c6495c8-fe09-490e-97df-9b5651d15ae4
-- title:
--   OAI.MUB6.Certificate.MixedSemantics.sound3109_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedSemantics.sound3109` of [lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound48.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound48.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedSemantics`):
--
--   ```lean
--   theorem sound3109_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
--       (_hF : AllTransitionsFourierZero B) :
--       mixedMoment B node3109 node3109Labels = Sparse.eval nodeValue3109 (mixedVector B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.AllTransitionsFourierZero` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedSemantics.Master` and `OAI.MUB6.Certificate.Sparse.eval` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.mixedMoment` (definitions bundle `OAIQ106E010` of this split); `OAI.MUB6.Certificate.MixedSemantics.node3109` and `OAI.MUB6.Certificate.MixedSemantics.node3109Labels` (definitions bundle `OAIQ106E079` of this split); `OAI.MUB6.Certificate.MixedSemantics.nodeValue3109` (definitions bundle `OAIQ106E084` of this split); `OAI.MUB6.Certificate.MixedSemantics.mixedVector` (definitions bundle `OAIQ106E086` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound591_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound607_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound48.lean (declaration OAI.MUB6.Certificate.MixedSemantics.sound3109)

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

theorem sound3109_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3109 node3109Labels = Sparse.eval nodeValue3109 (mixedVector B) := by
  sorry

end MUB6.Certificate.MixedSemantics

end OAI
end
