-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_trace_centered_mul_of_free
-- name    : OAI.KadisonSimilarity.trace_centered_mul_of_free
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T16:41:46.729486+00:00
-- url     : https://prove2.me/theorems/e024659e-3a46-46f8-9d2f-ef20e0733120
-- title:
--   OAI.KadisonSimilarity.trace_centered_mul_of_free: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.trace_centered_mul_of_free` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/FreeExpectation.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/FreeExpectation.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`):
--
--   ```lean
--   theorem trace_centered_mul_of_free
--       (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1) {P Q : StarSubalgebra ℂ R}
--       (hf : ScalarFree τ P Q) {a b : R} (ha : a ∈ P) (ha0 : τ a = 0) (hb : b ∈ Q) :
--       τ (a * b) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.ScalarFree` (definitions bundle `OAIQ075A004` of this split).
--
--   **Used by.** The proofs of `OAI.KadisonSimilarity.TracialCornerGeometry.all_degrees_propagation_of_published_words` and `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/FreeExpectation.lean (declaration OAI.KadisonSimilarity.trace_centered_mul_of_free)

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

theorem trace_centered_mul_of_free
    (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1) {P Q : StarSubalgebra ℂ R}
    (hf : ScalarFree τ P Q) {a b : R} (ha : a ∈ P) (ha0 : τ a = 0) (hb : b ∈ Q) :
    τ (a * b) = 0 := by
  sorry

end KadisonSimilarity

end

end OAI
end
