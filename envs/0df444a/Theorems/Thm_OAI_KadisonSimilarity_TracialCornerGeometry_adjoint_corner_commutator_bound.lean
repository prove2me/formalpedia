-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_adjoint_corner_commutator_bound
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.adjoint_corner_commutator_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T16:41:06.536191+00:00
-- url     : https://prove2.me/theorems/be4e2bae-26c5-4ee0-bd40-368301f6ccd6
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.adjoint_corner_commutator_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.adjoint_corner_commutator_bound` of [lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialAdjointBounds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialAdjointBounds.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`):
--
--   ```lean
--   theorem adjoint_corner_commutator_bound (e : P) (he : IsStarProjection e)
--       (Y : H →L[ℂ] H) {ε : ℝ}
--       (hY : ∀ x : CStarCorner e he, ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
--       (x : CStarCorner e he) :
--       ‖commutator Y.adjoint (G.left (x : P))‖ ≤ ε * ‖x‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.CStarCorner`, `OAI.KadisonSimilarity.TracialCornerGeometry` and `OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.commutator` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialAdjointBounds.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.adjoint_corner_commutator_bound)

import Mathlib
import Definitions.Def_KadisonSimilarity
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
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

theorem adjoint_corner_commutator_bound (e : P) (he : IsStarProjection e)
    (Y : H →L[ℂ] H) {ε : ℝ}
    (hY : ∀ x : CStarCorner e he, ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
    (x : CStarCorner e he) :
    ‖commutator Y.adjoint (G.left (x : P))‖ ≤ ε * ‖x‖ := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
