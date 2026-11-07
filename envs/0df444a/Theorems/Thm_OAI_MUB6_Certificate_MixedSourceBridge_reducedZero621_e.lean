-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_reducedZero621_e
-- name    : OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T17:42:21.235836+00:00
-- url     : https://prove2.me/theorems/eb987580-6a70-4f9e-8a04-ec5efed63b1e
-- title:
--   OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621` of [lean/OAI/Analysis/MutuallyUnbiased/MixedSources/Rows38.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSources/Rows38.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedSourceBridge`, with `open MixedSemantics`):
--
--   ```lean
--   theorem reducedZero621_e (B : Fin 7 → Basis) (hB : IsMUBFamily B)
--       (hF : AllTransitionsFourierZero B) :
--       reducedSource621 (mixedVector B) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.AllTransitionsFourierZero` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedSemantics.mixedVector` (definitions bundle `OAIQ106E086` of this split); `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource621` (definitions bundle `OAIQ106E127` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSources/Rows38.lean (declaration OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E127

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero621_e (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource621 (mixedVector B) = 0 := by
  sorry

end MUB6.Certificate.MixedSourceBridge

end OAI
end
