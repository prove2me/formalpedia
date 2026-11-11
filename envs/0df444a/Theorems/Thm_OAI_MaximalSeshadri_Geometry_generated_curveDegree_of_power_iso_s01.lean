-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_curveDegree_of_power_iso_s01
-- name    : OAI.MaximalSeshadri.Geometry.generated_curveDegree_of_power_iso_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:08:00.013642+00:00
-- url     : https://prove2.me/theorems/25050940-5a2d-4c22-ad01-ac62842beb19
-- title:
--   OAI.MaximalSeshadri.Geometry.generated_curveDegree_of_power_iso_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.generated_curveDegree_of_power_iso` of [lean/OAI/AlgebraicGeometry/Seshadri/Nodal/NodalNumericalDegree.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/NodalNumericalDegree.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective`):
--
--   ```lean
--   theorem generated_curveDegree_of_power_iso_s01 (S : Surface) (L : LineBundle S.scheme)
--       (hL : L.IsAmple) (M : LineBundle S.scheme) (d : ℕ) (e : M.sheaf ≅ (L.pow d).sheaf)
--       {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
--       (s : σ → (O S.scheme ⟶ M.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
--       (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
--       [IsIntegral (sectionIdeal k s hs v).subscheme]
--       (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1) :
--       let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
--         (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
--       curveDegree S L C = (d : ℤ)*selfIntersection S L
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Projective.sectionCombination` (definitions bundle `Q223SES006` of this split); `OAI.MaximalSeshadri.Projective.sectionIdeal` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.IntegralCurve`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.curveDegree`, `OAI.MaximalSeshadri.Geometry.selfIntersection` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/NodalNumericalDegree.lean (declaration OAI.MaximalSeshadri.Geometry.generated_curveDegree_of_power_iso)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem generated_curveDegree_of_power_iso_s01 (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (M : LineBundle S.scheme) (d : ℕ) (e : M.sheaf ≅ (L.pow d).sheaf)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ M.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1) :
    let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
    curveDegree S L C = (d : ℤ)*selfIntersection S L := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
