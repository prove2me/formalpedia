-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_power_H2_bounded_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.power_H2_bounded_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T14:55:57.646212+00:00
-- url     : https://prove2.me/theorems/b3884b3c-b996-421d-bf03-5bfd496859f0
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.power_H2_bounded_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.power_H2_bounded` of [lean/OAI/AlgebraicGeometry/Seshadri/Geometry/SurfaceTopGrowth.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/SurfaceTopGrowth.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective`):
--
--   ```lean
--   theorem Surface.power_H2_bounded_s01 (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
--       ∃ B : ℕ, ∀ n : ℕ, cohomologyDimension S.structureMap (L.pow n).sheaf 2 ≤ B
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.cohomologyDimension` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_arbitrary_jet_frames_s01`, `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_jets_s01`, `OAI.MaximalSeshadri.Geometry.Surface.positive_square_eventually_effective_s01` and `OAI.MaximalSeshadri.Geometry.Surface.square_squeeze_of_sections_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/SurfaceTopGrowth.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.power_H2_bounded)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES005

section

attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

theorem Surface.power_H2_bounded_s01 (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ B : ℕ, ∀ n : ℕ, cohomologyDimension S.structureMap (L.pow n).sheaf 2 ≤ B := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
