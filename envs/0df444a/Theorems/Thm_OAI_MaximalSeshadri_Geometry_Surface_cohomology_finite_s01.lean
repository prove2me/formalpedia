-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_cohomology_finite_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.cohomology_finite_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T14:44:37.147199+00:00
-- url     : https://prove2.me/theorems/8ae65cd7-e862-42ec-9b38-d77a212f9adf
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.cohomology_finite_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.cohomology_finite` of [lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SurfaceEuler.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SurfaceEuler.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace`):
--
--   ```lean
--   theorem Surface.cohomology_finite_s01 (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
--       (L : LineBundle S.scheme) (n : ℕ) :
--       letI := Module.compHom (cohomology L.sheaf n) (baseScalars S.structureMap)
--       Module.Finite ℂ (cohomology L.sheaf n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.baseScalars`, `OAI.MaximalSeshadri.Geometry.cohomology`, `OAI.MaximalSeshadri.Geometry.schemeHasExt`, `OAI.MaximalSeshadri.Geometry.sheafLinear`, `OAI.MaximalSeshadri.Geometry.structureSheaf` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.IntegralCurve.ideal_mixed_degree_s01`, `OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper_s01`, `OAI.MaximalSeshadri.Geometry.generated_curveDegree_of_power_iso_s01`, `OAI.MaximalSeshadri.Geometry.generated_power_euler_difference_s01`, `OAI.MaximalSeshadri.Geometry.generated_section_H2_untwist_s01` and `OAI.MaximalSeshadri.Geometry.generated_twist_euler_difference_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SurfaceEuler.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.cohomology_finite)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

theorem Surface.cohomology_finite_s01 (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) (n : ℕ) :
    letI := Module.compHom (cohomology L.sheaf n) (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology L.sheaf n) := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
