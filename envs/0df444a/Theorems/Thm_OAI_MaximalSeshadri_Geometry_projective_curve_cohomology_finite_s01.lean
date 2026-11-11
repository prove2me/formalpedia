-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_curve_cohomology_finite_s01
-- name    : OAI.MaximalSeshadri.Geometry.projective_curve_cohomology_finite_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:07:51.523787+00:00
-- url     : https://prove2.me/theorems/9e8c4fe7-0e22-476e-8a6f-606123ef1551
-- title:
--   OAI.MaximalSeshadri.Geometry.projective_curve_cohomology_finite_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.projective_curve_cohomology_finite` of [lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/ProjectiveCurveCohomology.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/ProjectiveCurveCohomology.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Projective MaximalSeshadri.Frames`):
--
--   ```lean
--   theorem projective_curve_cohomology_finite_s01
--       (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
--       (hd : topologicalKrullDim X = 1) {M : X.Modules}
--       (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
--       [IsClosedImmersion (sectionsMorphism
--         (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
--       (L : LineBundle X) (n : ℕ) :
--       letI := Module.compHom (cohomology L.sheaf n)
--         (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
--       Module.Finite K (cohomology L.sheaf n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Projective.sectionsMorphism` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.cohomology`, `OAI.MaximalSeshadri.Geometry.schemeHasExt`, `OAI.MaximalSeshadri.Geometry.sheafLinear` and `OAI.MaximalSeshadri.Geometry.structureSheaf` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.IntegralCurve.degree_nonneg_of_restriction_s01`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.ideal_mixed_degree_s01`, `OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper_s01`, `OAI.MaximalSeshadri.Geometry.curveDegree_tensor_s01`, `OAI.MaximalSeshadri.Geometry.generated_curveDegree_of_power_iso_s01`, `OAI.MaximalSeshadri.Geometry.generated_power_euler_difference_s01`, `OAI.MaximalSeshadri.Geometry.generated_section_H2_untwist_s01`, `OAI.MaximalSeshadri.Geometry.generated_twist_euler_difference_s01`, `OAI.MaximalSeshadri.Geometry.projective_curve_H1_le_s01`, `OAI.MaximalSeshadri.Geometry.projective_curve_power_euler_s01`, `OAI.MaximalSeshadri.Geometry.projective_nodal_degree_bound_s01`, `OAI.MaximalSeshadri.Geometry.projective_section_euler_difference_s01` and `OAI.MaximalSeshadri.Geometry.projective_section_positive_degree_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/ProjectiveCurveCohomology.lean (declaration OAI.MaximalSeshadri.Geometry.projective_curve_cohomology_finite)

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
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {K σ : Type} [Field K] [Infinite K] [Fintype σ]
    {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]

theorem projective_curve_cohomology_finite_s01
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
    (L : LineBundle X) (n : ℕ) :
    letI := Module.compHom (cohomology L.sheaf n)
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    Module.Finite K (cohomology L.sheaf n) := by
  sorry
end
end MaximalSeshadri.Geometry
end

end
end

end OAI
end
