-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ample_degree_positive_s01
-- name    : OAI.MaximalSeshadri.Geometry.IntegralCurve.ample_degree_positive_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T14:44:39.444725+00:00
-- url     : https://prove2.me/theorems/c5b05845-c110-49c3-bd7f-f871ff7b0186
-- title:
--   OAI.MaximalSeshadri.Geometry.IntegralCurve.ample_degree_positive_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.IntegralCurve.ample_degree_positive` of [lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SurfacePositiveSquare.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SurfacePositiveSquare.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace`):
--
--   ```lean
--   theorem IntegralCurve.ample_degree_positive_s01 (S : Surface) (C : IntegralCurve S)
--       (L : LineBundle S.scheme) (hL : L.IsAmple) : 0 < curveDegree S L C
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Geometry.IntegralCurve`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.curveDegree` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.Surface.effective_mixed_nonneg_s01`, `OAI.MaximalSeshadri.Geometry.Surface.eventual_etale_affine_section_test_s01`, `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_arbitrary_jet_frames_s01`, `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_jets_s01`, `OAI.MaximalSeshadri.Geometry.Surface.exists_all_section_quadrilateral_etale_s01`, `OAI.MaximalSeshadri.Geometry.Surface.positive_square_eventually_effective_s01`, `OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper_s01`, `OAI.MaximalSeshadri.Geometry.Surface.seshadri_eq_of_curve_lower_s01`, `OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01`, `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants` and `OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SurfacePositiveSquare.lean (declaration OAI.MaximalSeshadri.Geometry.IntegralCurve.ample_degree_positive)

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
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace

theorem IntegralCurve.ample_degree_positive_s01 (S : Surface) (C : IntegralCurve S)
    (L : LineBundle S.scheme) (hL : L.IsAmple) : 0 < curveDegree S L C := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
