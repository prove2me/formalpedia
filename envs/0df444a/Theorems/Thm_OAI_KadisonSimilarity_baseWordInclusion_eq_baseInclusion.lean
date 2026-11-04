-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_baseWordInclusion_eq_baseInclusion
-- name    : OAI.KadisonSimilarity.baseWordInclusion_eq_baseInclusion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T17:17:56.264024+00:00
-- url     : https://prove2.me/theorems/f29fd596-6257-45a1-b82f-419e9de70172
-- title:
--   OAI.KadisonSimilarity.baseWordInclusion_eq_baseInclusion: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.baseWordInclusion_eq_baseInclusion` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/WordBaseCoordinates.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/WordBaseCoordinates.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`):
--
--   ```lean
--   theorem baseWordInclusion_eq_baseInclusion
--       (hword : ∀ a : A,
--         baseWordInclusion (G.baseVector A 1) U ΩD hΩD (G.baseVector A a) = G.vector (a : P)) :
--       baseWordInclusion (G.baseVector A 1) U ΩD hΩD = G.baseInclusion A
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.CompletedTensorWord`, `OAI.KadisonSimilarity.OrthogonalWordLevels`, `OAI.KadisonSimilarity.TensorWord`, `OAI.KadisonSimilarity.TracialCornerGeometry`, `OAI.KadisonSimilarity.centeredSubspace`, `OAI.KadisonSimilarity.hilbertTensorInnerProductSpace`, `OAI.KadisonSimilarity.hilbertTensorNormedAddCommGroup`, `OAI.KadisonSimilarity.tensorWordSpace` and `OAI.KadisonSimilarity.TensorWordSpace` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.EndpointTensor` (definitions bundle `OAIQ075A009` of this split); `OAI.KadisonSimilarity.MultiplicityWordSpace`, `OAI.KadisonSimilarity.WordMultiplicity`, `OAI.KadisonSimilarity.baseWordInclusion`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace` and `OAI.KadisonSimilarity.TracialCornerGeometry.baseVector` (definitions bundle `OAIQ075A016` of this split).
--
--   **Used by.** The proofs of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` and `OAI.KadisonSimilarity.TracialCornerGeometry.tracial_baseWordInclusion_eq` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/WordBaseCoordinates.lean (declaration OAI.KadisonSimilarity.baseWordInclusion_eq_baseInclusion)

import Mathlib
import Definitions.Def_OAIQ075A016

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u} {B H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ΩA : B)
  (U : OrthogonalWordLevels (MultiplicityWordSpace (WordMultiplicity ΩA) E F) H)
  (ΩD : E) (hΩD : ‖ΩD‖ = 1)

section TracialBase
variable {P : Type*} [CStarAlgebra P]
  (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) E F) H)

theorem baseWordInclusion_eq_baseInclusion
    (hword : ∀ a : A,
      baseWordInclusion (G.baseVector A 1) U ΩD hΩD (G.baseVector A a) = G.vector (a : P)) :
    baseWordInclusion (G.baseVector A 1) U ΩD hΩD = G.baseInclusion A := by
  sorry

end TracialBase
end KadisonSimilarity

end

end OAI
end
