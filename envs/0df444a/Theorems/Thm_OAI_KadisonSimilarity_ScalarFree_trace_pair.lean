-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_ScalarFree_trace_pair
-- name    : OAI.KadisonSimilarity.ScalarFree.trace_pair
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T16:41:10.857671+00:00
-- url     : https://prove2.me/theorems/9ca6944b-5979-40a9-883d-6fc1f7bf079d
-- title:
--   OAI.KadisonSimilarity.ScalarFree.trace_pair: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.ScalarFree.trace_pair` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/FreeExpectation.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/FreeExpectation.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.ScalarFree`):
--
--   ```lean
--   theorem trace_pair {a b : R} (ha : a ∈ P) (hb : b ∈ Q)
--       (ha0 : τ a = 0) (hb0 : τ b = 0) : τ (a * b) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.ScalarFree` (definitions bundle `OAIQ075A004` of this split).
--
--   **Used by.** The proofs of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models` and `OAI.KadisonSimilarity.trace_centered_mul_of_free` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/FreeExpectation.lean (declaration OAI.KadisonSimilarity.ScalarFree.trace_pair)

import Mathlib
import Definitions.Def_OAIQ075A004

section

attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]

namespace ScalarFree

variable {τ : R →ₗ[ℂ] ℂ} {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)

include hf in
theorem trace_pair {a b : R} (ha : a ∈ P) (hb : b ∈ Q)
    (ha0 : τ a = 0) (hb0 : τ b = 0) : τ (a * b) = 0 := by
  sorry

end ScalarFree

end KadisonSimilarity

end

end OAI
end
