-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_weightedTerm26_e
-- name    : OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T05:53:01.257322+00:00
-- url     : https://prove2.me/theorems/de683a81-7053-4ef7-bbf9-1bafb0062d24
-- title:
--   OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26` of [lean/OAI/Analysis/MutuallyUnbiased/PairTargets/Weighted26.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairTargets/Weighted26.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.PairTargetSemantics`):
--
--   ```lean
--   theorem weightedTerm26_e {H : CMatrix} (hH : IsHadamard H) :
--       (47029248 : ℝ) * weightedAverage H term26 =
--         Integer.Sparse.eval integerTerm26 (PairSemantics.momentVector H)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.PairSemantics.momentVector` (definitions bundle `OAIQ106E071` of this split); `OAI.MUB6.Certificate.PairTargetSemantics.integerTerm26`, `OAI.MUB6.Certificate.PairTargetSemantics.term26` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedAverage` (definitions bundle `OAIQ106E140` of this split); `OAI.MUB6.CMatrix` and `OAI.MUB6.IsHadamard` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairTargets/Weighted26.lean (declaration OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26)

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E071
import Definitions.Def_OAIQ106E140

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

theorem weightedTerm26_e {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * weightedAverage H term26 =
      Integer.Sparse.eval integerTerm26 (PairSemantics.momentVector H) := by
  sorry

end MUB6.Certificate.PairTargetSemantics

end OAI
end
