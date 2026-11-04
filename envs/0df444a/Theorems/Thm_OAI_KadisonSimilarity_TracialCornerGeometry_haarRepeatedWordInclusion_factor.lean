-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_haarRepeatedWordInclusion_factor
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.haarRepeatedWordInclusion_factor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T17:20:26.45817+00:00
-- url     : https://prove2.me/theorems/0124de17-669e-4536-966f-316adc2dc00a
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.haarRepeatedWordInclusion_factor: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.haarRepeatedWordInclusion_factor` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialHaarWordColumns.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialHaarWordColumns.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`):
--
--   ```lean
--   theorem haarRepeatedWordInclusion_factor
--       (hU : TracialWordFormula G A D U)
--       (s : A) (hs0 : G.trace (s : P) = 0) (hsstar : star s = s) (hssq : s * s = 1)
--       (m n : ℕ) (b : A) :
--       G.haarRepeatedWordInclusion A D hτ U z ha htrace hhaar (m + 1) n
--         (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ (m + 1)
--           (G.baseVector A b)) =
--         G.left (tracialWordPrefix (ι := D.subtype) z a (s : P) m n)
--           (G.left ((haarCornerLetter z a n : D) : P)
--             (G.vector ((q : P) * (b : P))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.CStarCorner`, `OAI.KadisonSimilarity.CompletedTensorWord`, `OAI.KadisonSimilarity.HaarCornerMoments`, `OAI.KadisonSimilarity.OrthogonalWordLevels`, `OAI.KadisonSimilarity.TensorWord`, `OAI.KadisonSimilarity.TracialCornerGeometry`, `OAI.KadisonSimilarity.centeredSubspace`, `OAI.KadisonSimilarity.haarCornerLetter`, `OAI.KadisonSimilarity.hilbertTensorInnerProductSpace`, `OAI.KadisonSimilarity.hilbertTensorNormedAddCommGroup`, `OAI.KadisonSimilarity.tensorWordSpace`, `OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex` and `OAI.KadisonSimilarity.TensorWordSpace` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.EndpointTensor` (definitions bundle `OAIQ075A009` of this split); `OAI.KadisonSimilarity.MultiplicityWordSpace`, `OAI.KadisonSimilarity.WordMultiplicity`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace` and `OAI.KadisonSimilarity.TracialCornerGeometry.baseVector` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.TracialWordFormula`, `OAI.KadisonSimilarity.tracialWordPrefix` and `OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryRepeatedInclusion` (definitions bundle `OAIQ075A024` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.haarMultiplicityInnerFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.haarMultiplicityNormedFamily` and `OAI.KadisonSimilarity.TracialCornerGeometry.haarRepeatedWordInclusion` (definitions bundle `OAIQ075A029` of this split).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialHaarWordColumns.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.haarRepeatedWordInclusion_factor)

import Mathlib
import Definitions.Def_OAIQ075A029

section

attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

universe u v

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.haarMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.haarMultiplicityInnerFamily
variable (hτ : G.trace 1 = 1)
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)

include hτ z ha htrace hhaar

theorem haarRepeatedWordInclusion_factor
    (hU : TracialWordFormula G A D U)
    (s : A) (hs0 : G.trace (s : P) = 0) (hsstar : star s = s) (hssq : s * s = 1)
    (m n : ℕ) (b : A) :
    G.haarRepeatedWordInclusion A D hτ U z ha htrace hhaar (m + 1) n
      (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ (m + 1)
        (G.baseVector A b)) =
      G.left (tracialWordPrefix (ι := D.subtype) z a (s : P) m n)
        (G.left ((haarCornerLetter z a n : D) : P)
          (G.vector ((q : P) * (b : P)))) := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
