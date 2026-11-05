-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound1387_e
-- name    : OAI.MUB6.Certificate.PairSemantics.sound1387_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T02:02:24.282991+00:00
-- url     : https://prove2.me/theorems/8f48bc3c-83b3-416b-a27d-7c4c9b623240
-- title:
--   OAI.MUB6.Certificate.PairSemantics.sound1387_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.PairSemantics.sound1387` of [lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound21.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound21.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.PairSemantics`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem sound1387_e {H : CMatrix} (hH : IsHadamard H) :
--       injectiveMoment H node1387 = Sparse.eval value1387 (momentVector H)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.injectiveMoment` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.Sparse.eval` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.PairSemantics.momentVector` (definitions bundle `OAIQ106E071` of this split); `OAI.MUB6.Certificate.PairSemantics.value1387` (definitions bundle `OAIQ106E084` of this split); `OAI.MUB6.Certificate.PairSemantics.node1387` (definitions bundle `OAIQ106E119` of this split); `OAI.MUB6.CMatrix` and `OAI.MUB6.IsHadamard` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160_e` and `OAI.MUB6.Certificate.PairSourceBridge.rowSound66_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound21.lean (declaration OAI.MUB6.Certificate.PairSemantics.sound1387)

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E071
import Definitions.Def_OAIQ106E084
import Definitions.Def_OAIQ106E119

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1387_e {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1387 = Sparse.eval value1387 (momentVector H) := by
  sorry

end MUB6.Certificate.PairSemantics

end OAI
end
