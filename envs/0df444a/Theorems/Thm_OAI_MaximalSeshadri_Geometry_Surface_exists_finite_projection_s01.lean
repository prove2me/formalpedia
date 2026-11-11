-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_exists_finite_projection_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.exists_finite_projection_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:05:45.729202+00:00
-- url     : https://prove2.me/theorems/56aaebda-c645-45cf-a095-8bd97e53556f
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.exists_finite_projection_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.exists_finite_projection` of [lean/OAI/AlgebraicGeometry/Seshadri/Geometry/SurfaceProjection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/SurfaceProjection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Projective MaximalSeshadri.Frames`):
--
--   ```lean
--   theorem Surface.exists_finite_projection_s01 (S : Surface) (A : LineBundle S.scheme)
--       (hA : A.IsAmple) :
--       ∃ n : ℕ, 0 < n ∧ ∃ t : Fin 3 → (O S.scheme ⟶ (A.pow n).sheaf),
--         ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
--           IsFinite (sectionsMorphism (baseScalars S.structureMap) t ht)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Projective.sectionsMorphism` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.baseScalars` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.Surface.cohomology_finite_s01` and `OAI.MaximalSeshadri.Geometry.Surface.power_H2_bounded_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/SurfaceProjection.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.exists_finite_projection)

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

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames

theorem Surface.exists_finite_projection_s01 (S : Surface) (A : LineBundle S.scheme)
    (hA : A.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin 3 → (O S.scheme ⟶ (A.pow n).sheaf),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsFinite (sectionsMorphism (baseScalars S.structureMap) t ht) := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
