-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_exists_projective_sections_s01
-- name    : OAI.MaximalSeshadri.Geometry.IntegralCurve.exists_projective_sections_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:05:38.441207+00:00
-- url     : https://prove2.me/theorems/323c6f76-2799-4944-82b6-e4121fe20d24
-- title:
--   OAI.MaximalSeshadri.Geometry.IntegralCurve.exists_projective_sections_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.IntegralCurve.exists_projective_sections` of [lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SurfaceCurveDegree.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SurfaceCurveDegree.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective`, `open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets`, `open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal`, `open scoped Topology`):
--
--   ```lean
--   theorem IntegralCurve.exists_projective_sections_s01 (S : Surface) (C : IntegralCurve S)
--       (A : LineBundle S.scheme) (hA : LineBundle.IsAmple S.scheme A) :
--       ∃ σ : Type, ∃ _ : Fintype σ, ∃ M : C.scheme.Modules,
--         ∃ a : σ → (O C.scheme ⟶ M),
--         ∃ ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤,
--           IsClosedImmersion (sectionsMorphism (baseScalars (C.embedding ≫ S.structureMap)) a ha)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Projective.sectionsMorphism` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.IntegralCurve`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.baseScalars` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.IntegralCurve.ample_degree_positive_s01`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.cohomology_zero_above_one_s01`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.degree_nonneg_of_restriction_s01`, `OAI.MaximalSeshadri.Geometry.IntegralCurve.ideal_mixed_degree_s01`, `OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper_s01`, `OAI.MaximalSeshadri.Geometry.curveDegree_pow_s01`, `OAI.MaximalSeshadri.Geometry.curveDegree_tensor_s01`, `OAI.MaximalSeshadri.Geometry.generated_curveDegree_of_power_iso_s01`, `OAI.MaximalSeshadri.Geometry.generated_power_euler_difference_s01`, `OAI.MaximalSeshadri.Geometry.generated_section_H2_untwist_s01`, `OAI.MaximalSeshadri.Geometry.generated_twist_euler_difference_s01` and `OAI.MaximalSeshadri.Geometry.nodal_ideal_branch_sum_le_degree_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SurfaceCurveDegree.lean (declaration OAI.MaximalSeshadri.Geometry.IntegralCurve.exists_projective_sections)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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
open MaximalSeshadri.Frames MaximalSeshadri.Projective
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

theorem IntegralCurve.exists_projective_sections_s01 (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : LineBundle.IsAmple S.scheme A) :
    ∃ σ : Type, ∃ _ : Fintype σ, ∃ M : C.scheme.Modules,
      ∃ a : σ → (O C.scheme ⟶ M),
      ∃ ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤,
        IsClosedImmersion (sectionsMorphism (baseScalars (C.embedding ≫ S.structureMap)) a ha) := by
  sorry

end
end MaximalSeshadri.Geometry
end

end
end

end OAI
end
