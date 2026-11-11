-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_nodal_all_section_quadrilateral_s01
-- name    : OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:17:17.393625+00:00
-- url     : https://prove2.me/theorems/27c02ef1-e918-4133-916e-2fcbb39ed7d8
-- title:
--   OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral` of [lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/AllSectionQuadrilateral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/AllSectionQuadrilateral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.NodalLocal`, `open MaximalSeshadri.ProjectiveBertini`, `open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets`, `open MaximalSeshadri.LocalComparison`, `open scoped Topology`):
--
--   ```lean
--   theorem generated_nodal_all_section_quadrilateral_s01 (S : Surface)
--       (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
--       (d : ℕ) (hd : 0 < d) (E : M.sheaf ≅ (L.pow d).sheaf)
--       {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
--       (s : σ → (O S.scheme ⟶ M.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
--       (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
--       [IsIntegral (sectionIdeal k s hs v).subscheme]
--       (hDim : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1)
--       (U : S.scheme.affineOpens) (y : S.scheme) (hyU : y ∈ U.1)
--       (hyI : y ∈ (sectionIdeal k s hs v).support)
--       (eL : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
--       (eM : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
--       (hR : ringKrullDim Γ(S.scheme,U.1) ≤ 2) :
--       letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
--       let g := affineCoefficient U eM (sectionCombination k s v)
--       ∀ (q : (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ))
--         (hq : ∀ b, AnalyticAt ℂ (fun z => q z b) 0)
--         (_ : ∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
--           (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
--           (analyticTaylor q hq).toRingHom) = (RingHom.ker (q 0))^n ∧
--           Function.Surjective ((Ideal.Quotient.mk
--           (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
--           (analyticTaylor q hq).toRingHom))
--         (u : (ℂ × ℂ) → ℂ) (_ : AnalyticAt ℂ u 0) (_ : u 0 ≠ 0)
--         (_ : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) (_ : q 0 g = 0)
--         (a : ℕ) (_ : 0 < a) (t : O S.scheme ⟶ (L.pow a).sheaf) (_ : t ≠ 0)
--         (eA : (L.pow a).sheaf.restrict U.1.ι ≅ O U.1.toScheme)
--         (w : ℝ) (_ : 0 < w) (p : Exponent),
--         LexInitial (bivariateCoeff (bivariateTaylor q hq (affineCoefficient U eA t))) w p →
--         ((p.1:ℝ),(p.2:ℝ)) ∈ nodeQuadrilateral
--           ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)*w/(1+w)))
--           ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)/(1+w))) ((a:ℝ)/d)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Exponent` (definitions bundle `Q223SES000` of this split); `OAI.MaximalSeshadri.Frames.O` and `OAI.MaximalSeshadri.NodalLocal.Bivariate` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.ProjectiveBertini.openScalars` and `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.nodeQuadrilateral` (definitions bundle `Q223SES003` of this split); `OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor` and `OAI.MaximalSeshadri.AnalyticCoordinates.bivariateTaylor` (definitions bundle `Q223SES004` of this split); `OAI.MaximalSeshadri.LexInitial`, `OAI.MaximalSeshadri.NodalLocal.bivariateCoeff` and `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Projective.sectionCombination` (definitions bundle `Q223SES006` of this split); `OAI.MaximalSeshadri.Geometry.affineCoefficient` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Projective.sectionIdeal` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.selfIntersection` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.Surface.exists_all_section_quadrilateral_etale_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/AllSectionQuadrilateral.lean (declaration OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral)

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
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.NodalLocal
open MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison
open scoped Topology

theorem generated_nodal_all_section_quadrilateral_s01 (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    (d : ℕ) (hd : 0 < d) (E : M.sheaf ≅ (L.pow d).sheaf)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ M.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hDim : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1)
    (U : S.scheme.affineOpens) (y : S.scheme) (hyU : y ∈ U.1)
    (hyI : y ∈ (sectionIdeal k s hs v).support)
    (eL : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (eM : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hR : ringKrullDim Γ(S.scheme,U.1) ≤ 2) :
    letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
    let g := affineCoefficient U eM (sectionCombination k s v)
    ∀ (q : (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ))
      (hq : ∀ b, AnalyticAt ℂ (fun z => q z b) 0)
      (_ : ∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
        (analyticTaylor q hq).toRingHom) = (RingHom.ker (q 0))^n ∧
        Function.Surjective ((Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
        (analyticTaylor q hq).toRingHom))
      (u : (ℂ × ℂ) → ℂ) (_ : AnalyticAt ℂ u 0) (_ : u 0 ≠ 0)
      (_ : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) (_ : q 0 g = 0)
      (a : ℕ) (_ : 0 < a) (t : O S.scheme ⟶ (L.pow a).sheaf) (_ : t ≠ 0)
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
