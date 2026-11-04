-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_automorphism_alternatingProduct
-- name    : OAI.KadisonSimilarity.automorphism_alternatingProduct
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T17:17:07.01911+00:00
-- url     : https://prove2.me/theorems/52c1ad16-2cc6-43dd-92f0-e0151888fee5
-- title:
--   OAI.KadisonSimilarity.automorphism_alternatingProduct: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.automorphism_alternatingProduct` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialAutomorphismWords.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialAutomorphismWords.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`):
--
--   ```lean
--   theorem automorphism_alternatingProduct (θ : P ≃⋆ₐ[ℂ] P) {n : ℕ}
--       (a c : Fin n → P) :
--       θ (alternatingProduct a c) =
--         alternatingProduct (fun i => θ (a i)) (fun i => θ (c i))
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.alternatingProduct` (definitions bundle `OAIQ075A004` of this split).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialAutomorphismWords.lean (declaration OAI.KadisonSimilarity.automorphism_alternatingProduct)

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

attribute [local irreducible] tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem automorphism_alternatingProduct (θ : P ≃⋆ₐ[ℂ] P) {n : ℕ}
    (a c : Fin n → P) :
    θ (alternatingProduct a c) =
      alternatingProduct (fun i => θ (a i)) (fun i => θ (c i)) := by
  sorry

end KadisonSimilarity

end

end OAI
end
