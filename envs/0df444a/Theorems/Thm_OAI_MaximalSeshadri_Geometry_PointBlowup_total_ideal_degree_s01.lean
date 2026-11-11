-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_PointBlowup_total_ideal_degree_s01
-- name    : OAI.MaximalSeshadri.Geometry.PointBlowup.total_ideal_degree_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T14:49:02.257629+00:00
-- url     : https://prove2.me/theorems/2d71b9dc-f088-4979-b8c0-f3d20ba40283
-- title:
--   OAI.MaximalSeshadri.Geometry.PointBlowup.total_ideal_degree_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.PointBlowup.total_ideal_degree` of [lean/OAI/AlgebraicGeometry/Seshadri/Intersection/IdealProductDegree.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/IdealProductDegree.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace`, `open MaximalSeshadri.Frames`):
--
--   ```lean
--   theorem PointBlowup.total_ideal_degree_s01 (S : Surface) {r : ℕ} {p : Configuration S r}
--       (B : PointBlowup S r p) (A : LineBundle B.surface.scheme) (hA : A.IsAmple)
--       (J : LineBundle B.surface.scheme) (ι : J.sheaf ⟶ O B.surface.scheme)
--       (hJ : PresentsPullbackIdeal (centreIdeal S r p) B.projection J ι)
--       (C : IntegralCurve B.surface) :
--       curveDegree B.surface J C = ∑ i,curveDegree B.surface (B.exceptionalIdeal i) C
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Geometry.Configuration`, `OAI.MaximalSeshadri.Geometry.IntegralCurve`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.PointBlowup`, `OAI.MaximalSeshadri.Geometry.PresentsPullbackIdeal`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.centreIdeal`, `OAI.MaximalSeshadri.Geometry.curveDegree` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/IdealProductDegree.lean (declaration OAI.MaximalSeshadri.Geometry.PointBlowup.total_ideal_degree)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES001

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

theorem PointBlowup.total_ideal_degree_s01 (S : Surface) {r : ℕ} {p : Configuration S r}
    (B : PointBlowup S r p) (A : LineBundle B.surface.scheme) (hA : A.IsAmple)
    (J : LineBundle B.surface.scheme) (ι : J.sheaf ⟶ O B.surface.scheme)
    (hJ : PresentsPullbackIdeal (centreIdeal S r p) B.projection J ι)
    (C : IntegralCurve B.surface) :
    curveDegree B.surface J C = ∑ i,curveDegree B.surface (B.exceptionalIdeal i) C := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
