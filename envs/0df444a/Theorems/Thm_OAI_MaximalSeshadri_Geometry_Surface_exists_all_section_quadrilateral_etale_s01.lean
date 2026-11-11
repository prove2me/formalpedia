-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_exists_all_section_quadrilateral_etale_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.exists_all_section_quadrilateral_etale_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:01:35.807721+00:00
-- url     : https://prove2.me/theorems/6dd61e9f-0f2a-4c2c-bec3-aef887638489
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.exists_all_section_quadrilateral_etale_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.exists_all_section_quadrilateral_etale` of [lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/EtaleQuadrilateral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/EtaleQuadrilateral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini`, `open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets`, `open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal`, `open scoped Topology`):
--
--   ```lean
--   theorem Surface.exists_all_section_quadrilateral_etale_s01 (S : Surface)
--       (L : LineBundle S.scheme) (hL : L.IsAmple) :
--       ∃ d : ℕ, 0 < d ∧ ∃ y : S.scheme, ∃ U : S.scheme.affineOpens, ∃ hyU : y ∈ U.1,
--         ∃ _ : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
--         ∃ t : Fin 2 → Γ(S.scheme,U.1),
--           (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale ∧
--         letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
--         ∃ q : (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
--           RingHom.ker (q 0) = (U.2.isoSpec.hom ⟨y,hyU⟩).asIdeal ∧
--           ∃ hq : ∀ b, AnalyticAt ℂ (fun z => q z b) 0,
--           (∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
--             (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
--             (analyticTaylor q hq).toRingHom) = (RingHom.ker (q 0))^n ∧
--             Function.Surjective ((Ideal.Quotient.mk
--             (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
--             (analyticTaylor q hq).toRingHom)) ∧
--           Function.Injective (analyticTaylor q hq) ∧
--           (∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn q V) ∧
--           ∀ (a : ℕ) (_ : 0 < a) (t : O S.scheme ⟶ (L.pow a).sheaf) (_ : t ≠ 0)
--             (eA : (L.pow a).sheaf.restrict U.1.ι ≅ O U.1.toScheme)
--             (w : ℝ) (_ : 0 < w) (p : Exponent),
--             LexInitial (bivariateCoeff (bivariateTaylor q hq (affineCoefficient U eA t))) w p →
--             ((p.1:ℝ),(p.2:ℝ)) ∈ nodeQuadrilateral
--               ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)*w/(1+w)))
--               ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)/(1+w))) ((a:ℝ)/d)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Exponent` (definitions bundle `Q223SES000` of this split); `OAI.MaximalSeshadri.Frames.O` and `OAI.MaximalSeshadri.NodalLocal.Bivariate` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.ProjectiveBertini.openScalars` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.nodeQuadrilateral` (definitions bundle `Q223SES003` of this split); `OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor` and `OAI.MaximalSeshadri.AnalyticCoordinates.bivariateTaylor` (definitions bundle `Q223SES004` of this split); `OAI.MaximalSeshadri.LexInitial`, `OAI.MaximalSeshadri.NodalLocal.bivariateCoeff` and `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.affineCoefficient` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.selfIntersection` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.Surface.eventual_etale_affine_section_test_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/EtaleQuadrilateral.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.exists_all_section_quadrilateral_etale)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES003
import Definitions.Def_Q223SES007

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
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

theorem Surface.exists_all_section_quadrilateral_etale_s01 (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ∃ y : S.scheme, ∃ U : S.scheme.affineOpens, ∃ hyU : y ∈ U.1,
      ∃ _ : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ t : Fin 2 → Γ(S.scheme,U.1),
        (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale ∧
      letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
      ∃ q : (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
        RingHom.ker (q 0) = (U.2.isoSpec.hom ⟨y,hyU⟩).asIdeal ∧
        ∃ hq : ∀ b, AnalyticAt ℂ (fun z => q z b) 0,
        (∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
          (analyticTaylor q hq).toRingHom) = (RingHom.ker (q 0))^n ∧
          Function.Surjective ((Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
          (analyticTaylor q hq).toRingHom)) ∧
        Function.Injective (analyticTaylor q hq) ∧
        (∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn q V) ∧
        ∀ (a : ℕ) (_ : 0 < a) (t : O S.scheme ⟶ (L.pow a).sheaf) (_ : t ≠ 0)
          (eA : (L.pow a).sheaf.restrict U.1.ι ≅ O U.1.toScheme)
          (w : ℝ) (_ : 0 < w) (p : Exponent),
          LexInitial (bivariateCoeff (bivariateTaylor q hq (affineCoefficient U eA t))) w p →
          ((p.1:ℝ),(p.2:ℝ)) ∈ nodeQuadrilateral
            ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)*w/(1+w)))
            ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)/(1+w))) ((a:ℝ)/d) := by
  sorry
end
end MaximalSeshadri.Geometry

end

end OAI
end
