-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_extraCanonical124
-- name    : OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical124
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:35:28.660105+00:00
-- url     : https://prove2.me/theorems/ce70bd4b-3f79-43db-935a-d9c1a015c616
-- title:
--   OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical124: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical124` of [lean/OAI/Analysis/MutuallyUnbiased/PairTargets/ExtraCanonical7.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairTargets/ExtraCanonical7.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.PairTargetSemantics`, with `open MUB6.Certificate.PairSemantics`):
--
--   ```lean
--   theorem extraCanonical124 {H : CMatrix} (_hH : IsHadamard H) :
--       injectiveMoment H extraRaw124 = injectiveMoment H node1323
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.injectiveMoment` (definitions bundle `OAIQ106D000` of this split); `OAI.MUB6.Certificate.PairSemantics.node1323` (definitions bundle `OAIQ106D042` of this split); `OAI.MUB6.Certificate.PairTargetSemantics.extraRaw124` (definitions bundle `OAIQ106D068` of this split); `OAI.MUB6.CMatrix` and `OAI.MUB6.IsHadamard` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.PairTargetSemantics.partition25` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairTargets/ExtraCanonical7.lean (declaration OAI.MUB6.Certificate.PairTargetSemantics.extraCanonical124)

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D042
import Definitions.Def_OAIQ106D068

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics

theorem extraCanonical124 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H extraRaw124 = injectiveMoment H node1323 := by
  sorry

end MUB6.Certificate.PairTargetSemantics

end OAI
end
