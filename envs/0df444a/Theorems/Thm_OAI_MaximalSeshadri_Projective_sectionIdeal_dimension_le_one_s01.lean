-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_sectionIdeal_dimension_le_one_s01
-- name    : OAI.MaximalSeshadri.Projective.sectionIdeal_dimension_le_one_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:19:01.658933+00:00
-- url     : https://prove2.me/theorems/bb53835a-4fe9-49a2-b551-f52d6f3ce662
-- title:
--   OAI.MaximalSeshadri.Projective.sectionIdeal_dimension_le_one_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Projective.sectionIdeal_dimension_le_one` of [lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SectionDimension.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SectionDimension.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Projective`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Frames`):
--
--   ```lean
--   theorem sectionIdeal_dimension_le_one_s01 [IsIntegral X]
--       (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
--       (h : X ⟶ Proj (PolyGrade K τ)) [IsClosedImmersion h]
--       (hbase : h ≫ projectiveToSpec = g)
--       (L : LineBundle X) (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ L.sheaf))
--       (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → K)
--       (hv : sectionCombination k s v ≠ 0) :
--       topologicalKrullDim (sectionIdeal k s hs v).subscheme ≤ 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O`, `OAI.MaximalSeshadri.Projective.PolyGrade` and `OAI.MaximalSeshadri.Projective.projectiveToSpec` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Projective.sectionCombination` (definitions bundle `Q223SES006` of this split); `OAI.MaximalSeshadri.Projective.sectionIdeal` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale_s01`, `OAI.MaximalSeshadri.Geometry.Surface.coprime_integral_section_s01`, `OAI.MaximalSeshadri.Geometry.Surface.exists_finite_projection_s01` and `OAI.MaximalSeshadri.Geometry.Surface.lineBundle_cohomology_zero_above_two_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SectionDimension.lean (declaration OAI.MaximalSeshadri.Projective.sectionIdeal_dimension_le_one)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Frames

attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ τ : Type} [Field K] [Fintype σ] {X : Scheme}

theorem sectionIdeal_dimension_le_one_s01 [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K τ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (L : LineBundle X) (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → K)
    (hv : sectionCombination k s v ≠ 0) :
    topologicalKrullDim (sectionIdeal k s hs v).subscheme ≤ 1 := by
  sorry

end
end MaximalSeshadri.Projective
end

end
end

end OAI
end
