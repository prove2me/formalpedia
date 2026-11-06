-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_PairSemantics_sound3082_e
-- name    : OAI.MUB6.Certificate.PairSemantics.sound3082_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T01:31:52.191618+00:00
-- url     : https://prove2.me/theorems/ee86f65a-61ed-459f-b91b-7ed1f913fe96
-- title:
--   OAI.MUB6.Certificate.PairSemantics.sound3082_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.PairSemantics.sound3082` of [lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound48.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound48.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.PairSemantics`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem sound3082_e {H : CMatrix} (hH : IsHadamard H) :
--       injectiveMoment H node3082 = Sparse.eval value3082 (momentVector H)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.injectiveMoment` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.Sparse.eval` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.PairSemantics.momentVector` (definitions bundle `OAIQ106E071` of this split); `OAI.MUB6.Certificate.PairSemantics.node3082` (definitions bundle `OAIQ106E119` of this split); `OAI.MUB6.Certificate.PairSemantics.value3082` (definitions bundle `OAIQ106E148` of this split); `OAI.MUB6.CMatrix` and `OAI.MUB6.IsHadamard` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2193_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28_e` and `OAI.MUB6.Certificate.PairSourceBridge.rowSound32_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSemantics/Sound48.lean (declaration OAI.MUB6.Certificate.PairSemantics.sound3082)

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

theorem sound3082_e {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node3082 = Sparse.eval value3082 (momentVector H) := by
  sorry

end MUB6.Certificate.PairSemantics

end OAI
end
