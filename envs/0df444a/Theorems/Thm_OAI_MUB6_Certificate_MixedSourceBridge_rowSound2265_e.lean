-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2265_e
-- name    : OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-07T04:43:20.594452+00:00
-- url     : https://prove2.me/theorems/edd9da0a-9248-4077-86a2-926dffb47199
-- title:
--   OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265` of [lean/OAI/Analysis/MutuallyUnbiased/MixedSources/Rows141.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSources/Rows141.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedSourceBridge`, with `open MixedSemantics`):
--
--   ```lean
--   theorem rowSound2265_e (B : Fin 7 → Basis) (hB : IsMUBFamily B)
--       (_hF : AllTransitionsFourierZero B) :
--       Integer.Sparse.eval MixedData.row2265 (numericVector B) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.AllTransitionsFourierZero` and `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedData.row2265` (definitions bundle `OAIQ106E070` of this split); `OAI.MUB6.Certificate.MixedSemantics.numericVector` (definitions bundle `OAIQ106E086` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSources/Rows141.lean (declaration OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem rowSound2265_e (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2265 (numericVector B) = 0 := by
  sorry

end MUB6.Certificate.MixedSourceBridge

end OAI
end
