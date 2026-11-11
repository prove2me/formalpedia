-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_BaseSections_plane_boundaries_lift_s01
-- name    : OAI.MaximalSeshadri.Geometry.BaseSections.plane_boundaries_lift_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:00:27.546198+00:00
-- url     : https://prove2.me/theorems/27b136ba-8f12-4f68-bfba-ff24250d1065
-- title:
--   OAI.MaximalSeshadri.Geometry.BaseSections.plane_boundaries_lift_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.BaseSections.plane_boundaries_lift` of [lean/OAI/AlgebraicGeometry/Seshadri/Geometry/PlaneBoundaries.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/PlaneBoundaries.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry.BaseSections`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace`, `open MaximalSeshadri.Frames ModuleFlasque ModuleMayerVietoris MaximalSeshadri.Projective MaximalSeshadri.PlaneCech`):
--
--   ```lean
--   lemma plane_boundaries_lift_s01 :
--       vertexBoundaries (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2)
--         (planeVertex k s L) ≤ (relationBoundaries k s L).map (relationCycles k s L)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.PlaneCech.cycles`, `OAI.MaximalSeshadri.Geometry.BaseSections.BaseHom`, `OAI.MaximalSeshadri.Geometry.BaseSections.Sections`, `OAI.MaximalSeshadri.Geometry.BaseSections.baseHomGroup`, `OAI.MaximalSeshadri.Geometry.BaseSections.baseHomModule`, `OAI.MaximalSeshadri.Geometry.BaseSections.baseModule` and `OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Projective.planePair`, `OAI.MaximalSeshadri.Projective.planeTriple`, `OAI.MaximalSeshadri.Geometry.BaseSections.planeRelations` and `OAI.MaximalSeshadri.Geometry.BaseSections.relationBoundaries` (definitions bundle `Q223SES004` of this split); `OAI.MaximalSeshadri.PlaneCech.vertexBoundaries` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Projective.planeVertex` and `OAI.MaximalSeshadri.Geometry.BaseSections.relationCycles` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.finite_projection_H1_finite_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/PlaneBoundaries.lean (declaration OAI.MaximalSeshadri.Geometry.BaseSections.plane_boundaries_lift)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames ModuleFlasque ModuleMayerVietoris MaximalSeshadri.Projective MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}}
attribute [local instance] baseHomModule
variable (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X)

lemma plane_boundaries_lift_s01 :
    vertexBoundaries (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2)
      (planeVertex k s L) ≤ (relationBoundaries k s L).map (relationCycles k s L) := by
  sorry

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end
