-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3174_e
-- name    : OAI.MUB6.Certificate.PairSemantics.sound3174_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T02:20:34.897361+00:00
-- url     : https://prove2.me/theorems/5a847dc5-d012-46ed-926e-8d6159db0b3a
-- title:
--   OAI.MUB6.Certificate.PairSemantics.sound3174_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.PairSemantics.sound3174` of [lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.PairSemantics`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem sound3174_e {H : CMatrix} (hH : IsHadamard H) :
--       injectiveMoment H node3174 = Sparse.eval value3174 (momentVector H)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.injectiveMoment` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.Sparse.eval` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.PairSemantics.momentVector` (definitions bundle `OAIQ106E071` of this split); `OAI.MUB6.Certificate.PairSemantics.node3174` (definitions bundle `OAIQ106E119` of this split); `OAI.MUB6.Certificate.PairSemantics.value3174` (definitions bundle `OAIQ106E148` of this split); `OAI.MUB6.CMatrix` and `OAI.MUB6.IsHadamard` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293_e`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound_e` and `OAI.MUB6.Certificate.PairSourceBridge.rowSound14_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound49.lean (declaration OAI.MUB6.Certificate.PairSemantics.sound3174)

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E071
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E148

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound3174_e {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3174 = Sparse.eval value3174 (momentVector H) := by
  sorry

end MUB6.Certificate.PairSemantics

end OAI
end
