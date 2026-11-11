-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_etale_line_frame_inside_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.etale_line_frame_inside_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:14:17.502194+00:00
-- url     : https://prove2.me/theorems/b880d90b-e4cd-4bd6-b285-04d1f2316cd9
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.etale_line_frame_inside_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.etale_line_frame_inside` of [lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/EtaleLineFrame.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/EtaleLineFrame.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini MaximalSeshadri.AlgebraicJets`):
--
--   ```lean
--   lemma Surface.etale_line_frame_inside_s01 (S : Surface) (J : LineBundle S.scheme)
--       (W : S.scheme.Opens) (x : S.scheme) (hx : x ∈ W) :
--       ∃ U : S.scheme.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧
--         ∃ _ : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
--           ∃ t : Fin 2 → Γ(S.scheme,U.1),
--             (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.ProjectiveBertini.openScalars` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle` and `OAI.MaximalSeshadri.Geometry.Surface` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.Surface.ample_exceptional_square_squeeze_s01`, `OAI.MaximalSeshadri.Geometry.Surface.blowup_structureMap_isIso_s01`, `OAI.MaximalSeshadri.Geometry.Surface.seshadri_eq_of_curve_lower_s01`, `OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01` and `OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/EtaleLineFrame.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.etale_line_frame_inside)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES001
import Definitions.Def_Q223SES002

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini MaximalSeshadri.AlgebraicJets

lemma Surface.etale_line_frame_inside_s01 (S : Surface) (J : LineBundle S.scheme)
    (W : S.scheme.Opens) (x : S.scheme) (hx : x ∈ W) :
    ∃ U : S.scheme.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧
      ∃ _ : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        ∃ t : Fin 2 → Γ(S.scheme,U.1),
          (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
