-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_list_equal_square_orbit_comparison
-- name    : OAI.KadisonSimilarity.list_equal_square_orbit_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T08:22:24.227195+00:00
-- url     : https://prove2.me/theorems/337be945-47fe-4608-9327-21fe0027356e
-- title:
--   OAI.KadisonSimilarity.list_equal_square_orbit_comparison: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.list_equal_square_orbit_comparison` of [lean/OAI/Analysis/KadisonSimilarity/Representation/FiniteOrbitComparison.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/FiniteOrbitComparison.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`):
--
--   ```lean
--   theorem list_equal_square_orbit_comparison (π : BoundedUnitalHom A H)
--       {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖)
--       (a b : List A) (hab : listSquareSum a = listSquareSum b) (ξ : H) :
--       listOrbitSum π ξ a ≤ (2 * M ^ 4) ^ 2 * listOrbitSum π ξ b
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.listOrbitSum` and `OAI.KadisonSimilarity.listSquareSum` (definitions bundle `OAIQ075A006` of this split); `OAI.KadisonSimilarity.BoundedUnitalHom` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.similarityTheorem` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/FiniteOrbitComparison.lean (declaration OAI.KadisonSimilarity.list_equal_square_orbit_comparison)

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A006

section

attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem list_equal_square_orbit_comparison (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖)
    (a b : List A) (hab : listSquareSum a = listSquareSum b) (ξ : H) :
    listOrbitSum π ξ a ≤ (2 * M ^ 4) ^ 2 * listOrbitSum π ξ b := by
  sorry

end KadisonSimilarity

end

end OAI
end
