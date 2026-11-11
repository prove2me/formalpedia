-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_curve_H1_le_s01
-- name    : OAI.MaximalSeshadri.Geometry.projective_curve_H1_le_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:10:41.362196+00:00
-- url     : https://prove2.me/theorems/1b2f9772-0d9c-4d04-a31e-cd85d0f07fb6
-- title:
--   OAI.MaximalSeshadri.Geometry.projective_curve_H1_le_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.projective_curve_H1_le` of [lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/CurveH1Bound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/CurveH1Bound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective`):
--
--   ```lean
--   theorem projective_curve_H1_le_s01 {σ : Type} [Fintype σ]
--       (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
--       (hd : topologicalKrullDim X = 1) {A : X.Modules}
--       (a : σ → (O X ⟶ A)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
--       [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
--       (M : LineBundle X)
--       (hdeg : 0 ≤ eulerCharacteristic p 1 M.sheaf - eulerCharacteristic p 1 (O X)) :
--       cohomologyDimension p M.sheaf 1 ≤ cohomologyDimension p (O X) 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Projective.sectionsMorphism` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.baseScalars`, `OAI.MaximalSeshadri.Geometry.cohomologyDimension` and `OAI.MaximalSeshadri.Geometry.eulerCharacteristic` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper_s01` and `OAI.MaximalSeshadri.Geometry.generated_section_H2_untwist_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/CurveH1Bound.lean (declaration OAI.MaximalSeshadri.Geometry.projective_curve_H1_le)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

variable {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]

theorem projective_curve_H1_le_s01 {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {A : X.Modules}
    (a : σ → (O X ⟶ A)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (M : LineBundle X)
    (hdeg : 0 ≤ eulerCharacteristic p 1 M.sheaf - eulerCharacteristic p 1 (O X)) :
    cohomologyDimension p M.sheaf 1 ≤ cohomologyDimension p (O X) 1 := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
