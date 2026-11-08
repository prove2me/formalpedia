-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedData_false_of_gram_interpretation_e
-- name    : OAI.MUB6.Certificate.MixedData.false_of_gram_interpretation_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-07T19:43:49.110269+00:00
-- url     : https://prove2.me/theorems/02859681-a075-4a6c-a2ab-656514d039ce
-- title:
--   OAI.MUB6.Certificate.MixedData.false_of_gram_interpretation_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedData.false_of_gram_interpretation` of [lean/OAI/Analysis/MutuallyUnbiased/MixedMoments/MixedObstruction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedMoments/MixedObstruction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedData`):
--
--   ```lean
--   theorem false_of_gram_interpretation_e (B : Fin 7 → Basis) (hB : IsMUBFamily B)
--       (x : Fin 3237 → ℝ) (hx : ∀ i, |x i| ≤ 1) (hzero : x 0 = 1)
--       (hsources : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0)
--       (hgram : Integer.Combination.eval targetRows x rawCombination =
--         (denominator : ℝ) * GramNonnegative.sourceGram B) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedData.denominator` and `OAI.MUB6.Certificate.MixedData.rawCombination` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.GramNonnegative.sourceGram` (definitions bundle `OAIQ106E042` of this split); `OAI.MUB6.Certificate.Integer.Combination.eval` (definitions bundle `OAIQ106E051` of this split); `OAI.MUB6.Certificate.MixedData.sourceRows` (definitions bundle `OAIQ106E077` of this split); `OAI.MUB6.Certificate.MixedData.targetRows` (definitions bundle `OAIQ106E078` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proof of `OAI.MUB6.family_size_le_five_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedMoments/MixedObstruction.lean (declaration OAI.MUB6.Certificate.MixedData.false_of_gram_interpretation)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E042
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E078

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedData

theorem false_of_gram_interpretation_e (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (x : Fin 3237 → ℝ) (hx : ∀ i, |x i| ≤ 1) (hzero : x 0 = 1)
    (hsources : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0)
    (hgram : Integer.Combination.eval targetRows x rawCombination =
      (denominator : ℝ) * GramNonnegative.sourceGram B) : False := by
  sorry

end MUB6.Certificate.MixedData

end

end OAI
end
