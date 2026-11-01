-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_norm_spectral_arc_compression
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.norm_spectral_arc_compression
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T09:05:14.101455+00:00
-- url     : https://prove2.me/theorems/bf5392db-0e48-4fa9-addd-5061d99e92f2
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.norm_spectral_arc_compression: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.norm_spectral_arc_compression` of [lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialSpectralNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialSpectralNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`):
--
--   ```lean
--   theorem norm_spectral_arc_compression
--       (hS : (factorAlgebra (CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD)
--         (CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC)).topologicalClosure = S)
--       (published : RicardXuCompressionInput
--         ((G.halfCornerGeometry d hp htp).baseGeometry S)
--         ((CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD).comap S.subtype)
--         ((CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC).comap S.subtype))
--       (hfaithful : Function.Injective G.vector)
--       (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp G.trace)
--         (CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD)
--         (CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC))
--       (hdC : (d : P) ∈ C)
--       {θ : ℝ} (F : DihedralSpectralArc G.trace C w d θ)
--       (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi)
--       (e : CStarCorner (dihedralHalfProjection d) hp) (he : IsStarProjection e)
--       (heD : (e : P) ∈ D) {t : ℝ} (ht : 0 ≤ t) (hte : G.trace (e : P) = (t : ℂ))
--       (hwidth : 4 * θ ≤ 2 * t) :
--       ‖(e : P) * (F.element * dihedralHalfProjection d) * (e : P)‖ ≤ 3 * (2 * t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.KadisonSimilarity.CStarCorner`, `OAI.KadisonSimilarity.DihedralSpectralArc`, `OAI.KadisonSimilarity.ScalarFree`, `OAI.KadisonSimilarity.TracialCornerGeometry`, `OAI.KadisonSimilarity.cstarCornerSubalgebra_closed`, `OAI.KadisonSimilarity.dihedralHalfProjection`, `OAI.KadisonSimilarity.CStarCorner.instAlgebraComplexSubtypeMemNonUnitalStarSubalgebra`, `OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.normalizedTrace`, `OAI.KadisonSimilarity.CStarCorner.subalgebra` and `OAI.KadisonSimilarity.TracialCornerGeometry.factorAlgebra` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.isClosed_comap_subtype` (definitions bundle `OAIQ075A005` of this split); `OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace` and `OAI.KadisonSimilarity.TracialCornerGeometry.corner` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.RicardXuCompressionInput` (definitions bundle `OAIQ075A024` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.halfCornerGeometry` (definitions bundle `OAIQ075A029` of this split).
--
--   **Used by.** The proofs of `OAI_KadisonSimilarity_TracialCornerGeometry_exists_actual_spectral_test`, `OAI_KadisonSimilarity_TracialCornerGeometry_free_corner_from_local_models` and `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialSpectralNorm.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.norm_spectral_arc_compression)

import Mathlib
import Definitions.Def_OAIQ075A029

section

attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

variable (G : TracialCornerGeometry P H) (C D : StarSubalgebra ℂ P)
  [IsClosed (C : Set P)] [IsClosed (D : Set P)]
  (w d : Pˣ) (hp : IsStarProjection (dihedralHalfProjection d))
  (hpC : dihedralHalfProjection d ∈ C) (hpD : dihedralHalfProjection d ∈ D)
  (htp : G.trace (dihedralHalfProjection d) = (1 / 2 : ℂ))

variable
  (S : StarSubalgebra ℂ (CStarCorner (dihedralHalfProjection d) hp))
  [IsClosed (S : Set (CStarCorner (dihedralHalfProjection d) hp))]

theorem norm_spectral_arc_compression
    (hS : (factorAlgebra (CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC)).topologicalClosure = S)
    (published : RicardXuCompressionInput
      ((G.halfCornerGeometry d hp htp).baseGeometry S)
      ((CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD).comap S.subtype)
      ((CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC).comap S.subtype))
    (hfaithful : Function.Injective G.vector)
    (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp G.trace)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC))
    (hdC : (d : P) ∈ C)
    {θ : ℝ} (F : DihedralSpectralArc G.trace C w d θ)
    (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi)
    (e : CStarCorner (dihedralHalfProjection d) hp) (he : IsStarProjection e)
    (heD : (e : P) ∈ D) {t : ℝ} (ht : 0 ≤ t) (hte : G.trace (e : P) = (t : ℂ))
    (hwidth : 4 * θ ≤ 2 * t) :
    ‖(e : P) * (F.element * dihedralHalfProjection d) * (e : P)‖ ≤ 3 * (2 * t) := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
