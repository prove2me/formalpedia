-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_cyclicConstant_pos
-- name    : OAI.KadisonSimilarity.cyclicConstant_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T16:41:05.336207+00:00
-- url     : https://prove2.me/theorems/7640338d-3d65-4038-ae32-ea965f0646d1
-- title:
--   OAI.KadisonSimilarity.cyclicConstant_pos: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.cyclicConstant_pos` of [lean/OAI/Analysis/KadisonSimilarity/Constants.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Constants.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`):
--
--   ```lean
--   theorem cyclicConstant_pos : 0 < cyclicConstant
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.cyclicConstant` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** The proofs of `OAI.KadisonSimilarity.FiniteFactorModel.estimate`, `OAI.KadisonSimilarity.TracialCornerGeometry.all_degrees_propagation_of_published_words`, `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` and `OAI.KadisonSimilarity.finite_standard_bound_of_local_free_corner` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Constants.lean (declaration OAI.KadisonSimilarity.cyclicConstant_pos)

import Mathlib
import Definitions.Def_KadisonSimilarity

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KadisonSimilarity

theorem cyclicConstant_pos : 0 < cyclicConstant := by
  sorry

end KadisonSimilarity

end

end OAI
end
