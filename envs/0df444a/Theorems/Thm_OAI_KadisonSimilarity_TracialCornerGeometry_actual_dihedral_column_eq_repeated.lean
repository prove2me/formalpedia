-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_actual_dihedral_column_eq_repeated
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.actual_dihedral_column_eq_repeated
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T16:42:05.660449+00:00
-- url     : https://prove2.me/theorems/fcbed6cf-1ec0-4952-97ff-dac5f366d507
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.actual_dihedral_column_eq_repeated: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.actual_dihedral_column_eq_repeated` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/DihedralColumnIdentification.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/DihedralColumnIdentification.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`):
--
--   ```lean
--   theorem actual_dihedral_column_eq_repeated (hf : ScalarFree G.trace D A)
--       (hU : TracialWordFormula G A D U) (k : ℕ) (v : G.baseSpace A) :
--       G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
--         he ht hte k v =
--       G.repeatedDihedralInclusion D A hτ d s e hdstar hdsq hd0 hsstar hssq hs0
--         he ht hte U k v
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.CompletedTensorWord`, `OAI.KadisonSimilarity.OrthogonalWordLevels`, `OAI.KadisonSimilarity.ScalarFree`, `OAI.KadisonSimilarity.TensorWord`, `OAI.KadisonSimilarity.TracialCornerGeometry`, `OAI.KadisonSimilarity.centeredSubspace`, `OAI.KadisonSimilarity.hilbertTensorInnerProductSpace`, `OAI.KadisonSimilarity.hilbertTensorNormedAddCommGroup`, `OAI.KadisonSimilarity.tensorWordSpace` and `OAI.KadisonSimilarity.TensorWordSpace` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.EndpointTensor` (definitions bundle `OAIQ075A009` of this split); `OAI.KadisonSimilarity.MultiplicityWordSpace`, `OAI.KadisonSimilarity.WordMultiplicity`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseVector`, `OAI.KadisonSimilarity.TracialCornerGeometry.dihedralMultiplicityInnerFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.dihedralMultiplicityNormedFamily` and `OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.TracialWordFormula` and `OAI.KadisonSimilarity.TracialCornerGeometry.repeatedDihedralInclusion` (definitions bundle `OAIQ075A024` of this split).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/DihedralColumnIdentification.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.actual_dihedral_column_eq_repeated)

import Mathlib
import Definitions.Def_OAIQ075A024

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (D A : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  (hτ : G.trace 1 = 1)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))

attribute [local instance] dihedralMultiplicityNormedFamily dihedralMultiplicityInnerFamily

variable
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)

attribute [local irreducible] tracialDihedralInclusion

theorem actual_dihedral_column_eq_repeated (hf : ScalarFree G.trace D A)
    (hU : TracialWordFormula G A D U) (k : ℕ) (v : G.baseSpace A) :
    G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte k v =
    G.repeatedDihedralInclusion D A hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte U k v := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
