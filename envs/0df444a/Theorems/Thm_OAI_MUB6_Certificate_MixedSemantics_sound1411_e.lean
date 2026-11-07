-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound1411_e
-- name    : OAI.MUB6.Certificate.MixedSemantics.sound1411_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T14:14:09.713523+00:00
-- url     : https://prove2.me/theorems/9ad7ac39-7a68-4598-a999-b5d72ff3e9c1
-- title:
--   OAI.MUB6.Certificate.MixedSemantics.sound1411_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedSemantics.sound1411` of [lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound22.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound22.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedSemantics`):
--
--   ```lean
--   theorem sound1411_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
--       (_hF : AllTransitionsFourierZero B) :
--       mixedMoment B node1411 node1411Labels = Sparse.eval nodeValue1411 (mixedVector B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.AllTransitionsFourierZero` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedSemantics.Master` and `OAI.MUB6.Certificate.Sparse.eval` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.mixedMoment` (definitions bundle `OAIQ106E010` of this split); `OAI.MUB6.Certificate.MixedSemantics.node1411` and `OAI.MUB6.Certificate.MixedSemantics.node1411Labels` (definitions bundle `OAIQ106E079` of this split); `OAI.MUB6.Certificate.MixedSemantics.nodeValue1411` (definitions bundle `OAIQ106E084` of this split); `OAI.MUB6.Certificate.MixedSemantics.mixedVector` (definitions bundle `OAIQ106E086` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound22.lean (declaration OAI.MUB6.Certificate.MixedSemantics.sound1411)

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

theorem sound1411_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1411 node1411Labels = Sparse.eval nodeValue1411 (mixedVector B) := by
  sorry

end MUB6.Certificate.MixedSemantics

end OAI
end
