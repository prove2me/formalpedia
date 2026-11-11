-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_twistedIdealPowerInclusion_ideal_s01
-- name    : OAI.MaximalSeshadri.Geometry.twistedIdealPowerInclusion_ideal_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:17:17.306147+00:00
-- url     : https://prove2.me/theorems/9d118874-dce7-495d-b6eb-bf49925efb42
-- title:
--   OAI.MaximalSeshadri.Geometry.twistedIdealPowerInclusion_ideal_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.twistedIdealPowerInclusion_ideal` of [lean/OAI/AlgebraicGeometry/Seshadri/LocalAlgebra/TwistedIdealPower.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/LocalAlgebra/TwistedIdealPower.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames`):
--
--   ```lean
--   lemma twistedIdealPowerInclusion_ideal_s01 (L J : LineBundle X) (ι : J.sheaf ⟶ O X)
--       (a b n : ℕ) (U : X.affineOpens)
--       (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
--       (f : (L.pow (a*n)).sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
--       Ideal.span {affineMapCoefficient U (twistedIdealPowerFrame L J a b n U.1 e f)
--         f (twistedIdealPowerInclusion L J ι a b n)} =
--       (Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι})^(b*n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.affineMapCoefficient`, `OAI.MaximalSeshadri.Geometry.twistedIdealPowerFrame`, `OAI.MaximalSeshadri.Geometry.twistedIdealPowerInclusion` and `OAI.MaximalSeshadri.Geometry.LineBundle.tensor` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/LocalAlgebra/TwistedIdealPower.lean (declaration OAI.MaximalSeshadri.Geometry.twistedIdealPowerInclusion_ideal)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma twistedIdealPowerInclusion_ideal_s01 (L J : LineBundle X) (ι : J.sheaf ⟶ O X)
    (a b n : ℕ) (U : X.affineOpens)
    (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : (L.pow (a*n)).sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {affineMapCoefficient U (twistedIdealPowerFrame L J a b n U.1 e f)
      f (twistedIdealPowerInclusion L J ι a b n)} =
    (Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι})^(b*n) := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
