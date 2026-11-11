-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_planeVertex_finite_generators_s01
-- name    : OAI.MaximalSeshadri.Projective.planeVertex_finite_generators_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:18:44.288697+00:00
-- url     : https://prove2.me/theorems/a52bbc4e-e442-4d8e-afe0-891e89d9d901
-- title:
--   OAI.MaximalSeshadri.Projective.planeVertex_finite_generators_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Projective.planeVertex_finite_generators` of [lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/PlaneVertex.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/PlaneVertex.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Projective`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames`, `open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech`):
--
--   ```lean
--   lemma planeVertex_finite_generators_s01 (k : K →+* Γ(X,⊤))
--       (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
--       [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) (i : Fin 3) :
--       letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
--         (L.sheaf.restrict (planeTriple s).ι)
--       ∃ d : ℕ, ∃ g : Fin d → Sections ((planeTriple s).ι.appTop.hom.comp k)
--         (L.sheaf.restrict (planeTriple s).ι) ⊤,
--         (∀ a, g a ∈ planeVertex k s L i) ∧
--         planeVertex k s L i = monomialSpan (K := K) (vertexCone i) g
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.PlaneCech.vertexCone`, `OAI.MaximalSeshadri.SectionOpens.isoOpen`, `OAI.MaximalSeshadri.Geometry.BaseSections.Sections`, `OAI.MaximalSeshadri.Geometry.BaseSections.baseModule`, `OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections` and `OAI.MaximalSeshadri.Geometry.BaseSections.laurentModule` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Projective.planeTriple` (definitions bundle `Q223SES004` of this split); `OAI.MaximalSeshadri.PlaneCech.monomialSpan` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Projective.planeVertex` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Projective.planeX` and `OAI.MaximalSeshadri.Projective.planeY` (definitions bundle `Q223SES008` of this split); `OAI.MaximalSeshadri.Projective.sectionsMorphism` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Projective.finite_plane_H1_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/PlaneVertex.lean (declaration OAI.MaximalSeshadri.Projective.planeVertex_finite_generators)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

lemma planeVertex_finite_generators_s01 (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) (i : Fin 3) :
    letI := laurentModule ((planeTriple s).ι.appTop.hom.comp k) (planeX s) (planeY s)
      (L.sheaf.restrict (planeTriple s).ι)
    ∃ d : ℕ, ∃ g : Fin d → Sections ((planeTriple s).ι.appTop.hom.comp k)
      (L.sheaf.restrict (planeTriple s).ι) ⊤,
      (∀ a, g a ∈ planeVertex k s L i) ∧
      planeVertex k s L i = monomialSpan (K := K) (vertexCone i) g := by
  sorry

end
end MaximalSeshadri.Projective

end

end OAI
end
