-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5492_e
-- name    : OAI.MUB6.Certificate.MixedSemantics.sound5492_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T17:26:47.594959+00:00
-- url     : https://prove2.me/theorems/ce62d34c-539c-4b3a-8d09-b2c278275bfc
-- title:
--   OAI.MUB6.Certificate.MixedSemantics.sound5492_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedSemantics.sound5492` of [lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound85.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound85.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedSemantics`):
--
--   ```lean
--   theorem sound5492_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
--       (_hF : AllTransitionsFourierZero B) :
--       mixedMoment B node5492 node5492Labels = Sparse.eval nodeValue5492 (mixedVector B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.AllTransitionsFourierZero` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedSemantics.Master` and `OAI.MUB6.Certificate.Sparse.eval` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.mixedMoment` (definitions bundle `OAIQ106E010` of this split); `OAI.MUB6.Certificate.MixedSemantics.node5492` and `OAI.MUB6.Certificate.MixedSemantics.node5492Labels` (definitions bundle `OAIQ106E081` of this split); `OAI.MUB6.Certificate.MixedSemantics.nodeValue5492` (definitions bundle `OAIQ106E084` of this split); `OAI.MUB6.Certificate.MixedSemantics.mixedVector` (definitions bundle `OAIQ106E086` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Sound85.lean (declaration OAI.MUB6.Certificate.MixedSemantics.sound5492)

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

theorem sound5492_e (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5492 node5492Labels = Sparse.eval nodeValue5492 (mixedVector B) := by
  sorry

end MUB6.Certificate.MixedSemantics

end OAI
end
