-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_lift_section_of_local_ideal_power_s01
-- name    : OAI.MaximalSeshadri.Geometry.lift_section_of_local_ideal_power_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:17:06.579197+00:00
-- url     : https://prove2.me/theorems/1369e2ec-1e77-4766-9c33-3a3f34f52e58
-- title:
--   OAI.MaximalSeshadri.Geometry.lift_section_of_local_ideal_power_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.lift_section_of_local_ideal_power` of [lean/OAI/AlgebraicGeometry/Seshadri/Divisors/IdealSectionLifting.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/IdealSectionLifting.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini`):
--
--   ```lean
--   theorem lift_section_of_local_ideal_power_s01 (f : Y ⟶ X) (I : X.IdealSheafData)
--       (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
--       (M : LineBundle X) (n : ℕ) (s : O X ⟶ M.sheaf)
--       (hs : ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 ∧
--         ∃ e : M.sheaf.restrict V.1.ι ≅ O V.1.toScheme,
--           affineCoefficient V e s ∈ (I.ideal V)^n) :
--       ∃! q : O Y ⟶ ((J.pow n).tensor (M.pullback f)).sheaf,
--         q ≫ tensorInclusion (J.pow n) (M.pullback f) (idealPowerInclusion J ι n) =
--           pullbackSection f s
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pullback` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.pullbackSection` and `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.affineCoefficient`, `OAI.MaximalSeshadri.Geometry.idealPowerInclusion`, `OAI.MaximalSeshadri.Geometry.tensorInclusion` and `OAI.MaximalSeshadri.Geometry.LineBundle.tensor` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle` and `OAI.MaximalSeshadri.Geometry.PresentsPullbackIdeal` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.Surface.ample_exceptional_square_squeeze_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/IdealSectionLifting.lean (declaration OAI.MaximalSeshadri.Geometry.lift_section_of_local_ideal_power)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

theorem lift_section_of_local_ideal_power_s01 (f : Y ⟶ X) (I : X.IdealSheafData)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (M : LineBundle X) (n : ℕ) (s : O X ⟶ M.sheaf)
    (hs : ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 ∧
      ∃ e : M.sheaf.restrict V.1.ι ≅ O V.1.toScheme,
        affineCoefficient V e s ∈ (I.ideal V)^n) :
    ∃! q : O Y ⟶ ((J.pow n).tensor (M.pullback f)).sheaf,
      q ≫ tensorInclusion (J.pow n) (M.pullback f) (idealPowerInclusion J ι n) =
        pullbackSection f s := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
