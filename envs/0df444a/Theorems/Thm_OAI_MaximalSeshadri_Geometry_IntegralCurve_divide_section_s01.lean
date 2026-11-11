-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_divide_section_s01
-- name    : OAI.MaximalSeshadri.Geometry.IntegralCurve.divide_section_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:17:08.262195+00:00
-- url     : https://prove2.me/theorems/e24b3a1d-366d-4012-9594-08c57186c6fe
-- title:
--   OAI.MaximalSeshadri.Geometry.IntegralCurve.divide_section_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.IntegralCurve.divide_section` of [lean/OAI/AlgebraicGeometry/Seshadri/Divisors/CartierResidual.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/CartierResidual.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini`):
--
--   ```lean
--   theorem IntegralCurve.divide_section_s01 (S : Surface) (C : IntegralCurve S)
--       (J M : LineBundle S.scheme) (ι : J.sheaf ⟶ O S.scheme)
--       (hJ : PresentsPullbackIdeal C.embedding.ker (𝟙 S.scheme) J ι)
--       (s : O S.scheme ⟶ M.sheaf) (hs : pullbackSection C.embedding s = 0) :
--       ∃! q : O S.scheme ⟶ (J.tensor M).sheaf, q ≫ tensorInclusion J M ι = s
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Geometry.pullbackSection` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.tensorInclusion` and `OAI.MaximalSeshadri.Geometry.LineBundle.tensor` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.IntegralCurve`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.PresentsPullbackIdeal` and `OAI.MaximalSeshadri.Geometry.Surface` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/CartierResidual.lean (declaration OAI.MaximalSeshadri.Geometry.IntegralCurve.divide_section)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

theorem IntegralCurve.divide_section_s01 (S : Surface) (C : IntegralCurve S)
    (J M : LineBundle S.scheme) (ι : J.sheaf ⟶ O S.scheme)
    (hJ : PresentsPullbackIdeal C.embedding.ker (𝟙 S.scheme) J ι)
    (s : O S.scheme ⟶ M.sheaf) (hs : pullbackSection C.embedding s = 0) :
    ∃! q : O S.scheme ⟶ (J.tensor M).sheaf, q ≫ tensorInclusion J M ι = s := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
