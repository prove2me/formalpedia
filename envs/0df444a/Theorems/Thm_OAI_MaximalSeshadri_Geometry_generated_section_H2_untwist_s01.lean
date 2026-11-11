-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_section_H2_untwist_s01
-- name    : OAI.MaximalSeshadri.Geometry.generated_section_H2_untwist_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:07:51.413658+00:00
-- url     : https://prove2.me/theorems/75ffde45-f494-4925-9e18-ed3fcba95d4c
-- title:
--   OAI.MaximalSeshadri.Geometry.generated_section_H2_untwist_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.generated_section_H2_untwist` of [lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/SurfaceH2Untwist.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/SurfaceH2Untwist.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective`):
--
--   ```lean
--   theorem generated_section_H2_untwist_s01 (S : Surface)
--       (A : LineBundle S.scheme) (hA : A.IsAmple) (L M : LineBundle S.scheme)
--       {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
--       (s : σ → (O S.scheme ⟶ L.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
--       (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
--       [IsIntegral (sectionIdeal k s hs v).subscheme]
--       (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1)
--       (hdeg : let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
--         (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
--         0 ≤ curveDegree S (L.tensor M) C) :
--       cohomologyDimension S.structureMap M.sheaf 2 ≤
--         cohomologyDimension ((sectionIdeal k s hs v).subschemeι ≫ S.structureMap)
--           (O (sectionIdeal k s hs v).subscheme) 1 +
--         cohomologyDimension S.structureMap (L.tensor M).sheaf 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Projective.sectionCombination` (definitions bundle `Q223SES006` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.tensor` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Projective.sectionIdeal` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.IntegralCurve`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.cohomologyDimension`, `OAI.MaximalSeshadri.Geometry.curveDegree` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_arbitrary_jet_frames_s01`, `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_jets_s01` and `OAI.MaximalSeshadri.Geometry.Surface.positive_square_eventually_effective_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/SurfaceH2Untwist.lean (declaration OAI.MaximalSeshadri.Geometry.generated_section_H2_untwist)

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
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem generated_section_H2_untwist_s01 (S : Surface)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L M : LineBundle S.scheme)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ L.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1)
    (hdeg : let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
      0 ≤ curveDegree S (L.tensor M) C) :
    cohomologyDimension S.structureMap M.sheaf 2 ≤
      cohomologyDimension ((sectionIdeal k s hs v).subschemeι ≫ S.structureMap)
        (O (sectionIdeal k s hs v).subscheme) 1 +
      cohomologyDimension S.structureMap (L.tensor M).sheaf 2 := by
  sorry
end
end MaximalSeshadri.Geometry

end

end OAI
end
