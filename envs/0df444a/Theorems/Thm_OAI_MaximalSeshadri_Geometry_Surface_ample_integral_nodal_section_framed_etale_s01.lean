-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_ample_integral_nodal_section_framed_etale_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:07:13.960962+00:00
-- url     : https://prove2.me/theorems/a4008a52-f702-402d-b23a-cc41dd055585
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale` of [lean/OAI/AlgebraicGeometry/Seshadri/Nodal/EtaleNodalDivisor.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/EtaleNodalDivisor.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini`, `open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets`, `open MaximalSeshadri.AnalyticCoordinates`, `open scoped Topology`):
--
--   ```lean
--   theorem Surface.ample_integral_nodal_section_framed_etale_s01 (S : Surface)
--       (L : LineBundle S.scheme) (hL : LineBundle.IsAmple S.scheme L) :
--       ∃ d : ℕ, 0 < d ∧ ∃ N : ℕ,
--         ∃ s : Option (Fin N) → GlobalSections S.scheme (modulePow S.scheme L.sheaf d),
--         ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
--         ∃ y : S.scheme, ∃ U : S.scheme.affineOpens, ∃ hyU : y ∈ U.1,
--         ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
--         ∃ _ : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
--         ∃ t : Fin 2 → Γ(S.scheme,U.1),
--           (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale ∧
--           let k := S.structureMap.appTop.hom.comp
--             (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
--           let _ : Algebra ℂ Γ(S.scheme, U.1) := (openScalars S.structureMap U.1).toAlgebra
--           ∃ v : QuarticIndex (Fin N) → ℂ,
--             (∀ x : S.scheme, x ∉ centeredOpen s ↔ x = y) ∧
--             IsIntegral (doublePointQuarticIdeal k s hs v).subscheme ∧
--             topologicalKrullDim (doublePointQuarticIdeal k s hs v).subscheme = 1 ∧
--             InvertiblePullbackIdeal (doublePointQuarticIdeal k s hs v) (𝟙 S.scheme) ∧
--             y ∈ (doublePointQuarticIdeal k s hs v).support ∧
--             sectionCombination k (doublePointQuartics s) v ≠ 0 ∧
--             Smooth (((doublePointQuarticIdeal k s hs v).comap (centeredOpen s).ι).subschemeι ≫
--               (centeredOpen s).ι ≫ S.structureMap) ∧
--             let f := U.1.topIso.hom (coefficient
--               (sectionFrameOn (powerSection (s none) 4) U.1
--                 (hU.trans (sectionOpen_le_powerSection (s none) 4)))
--               (restrictSection U.1.ι (sectionCombination k (doublePointQuartics s) v)))
--             ∃ q : (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
--               ringKrullDim Γ(S.scheme,U.1) ≤ 2 ∧ (Ideal.span {f}).IsPrime ∧
--               f ≠ 0 ∧ q 0 f = 0 ∧
--               RingHom.ker (q 0) = (U.2.isoSpec.hom ⟨y,hyU⟩).asIdeal ∧
--               ∃ hq : (∀ a, AnalyticAt ℂ (fun z => q z a) 0),
--               ∃ u : (ℂ × ℂ) → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
--                 (∀ᶠ z in 𝓝 0, q z f = u z*z.1*z.2) ∧
--                 (∃ i : Fin 2 → Fin N, ∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ),
--                   HasFDerivAt (fun z =>
--                     (q z (-affineSectionRatios s U hU (some (i 1))),
--                      q z (-affineSectionRatios s U hU (some (i 0)))))
--                     (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
--                 (∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
--                   (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
--                   (analyticTaylor q hq).toRingHom) =
--                     (U.2.isoSpec.hom ⟨y,hyU⟩).asIdeal^n ∧
--                   Function.Surjective ((Ideal.Quotient.mk
--                     (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
--                     (analyticTaylor q hq).toRingHom)) ∧
--                 Function.Injective (analyticTaylor q hq) ∧
--                 ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn q V
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Geometry.powerSection` (definitions bundle `Q223SES000` of this split); `OAI.MaximalSeshadri.Frames.O` and `OAI.MaximalSeshadri.Frames.coefficient` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Projective.QuarticIndex`, `OAI.MaximalSeshadri.ProjectiveBertini.openScalars` and `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor`, `OAI.MaximalSeshadri.Frames.restrictSection` and `OAI.MaximalSeshadri.Projective.sectionFrameOn` (definitions bundle `Q223SES004` of this split); `OAI.MaximalSeshadri.Geometry.sectionOpen_le_powerSection` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Projective.sectionCombination` (definitions bundle `Q223SES006` of this split); `OAI.MaximalSeshadri.Projective.affineSectionRatios` and `OAI.MaximalSeshadri.Projective.doublePointQuartics` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Projective.centeredOpen` and `OAI.MaximalSeshadri.Projective.doublePointQuarticIdeal` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.GlobalSections`, `OAI.MaximalSeshadri.Geometry.InvertiblePullbackIdeal`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.modulePow`, `OAI.MaximalSeshadri.Geometry.structureSheaf` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.Surface.exists_all_section_quadrilateral_etale_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/EtaleNodalDivisor.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets
open MaximalSeshadri.AnalyticCoordinates
open scoped Topology

attribute [local instance] MvPolynomial.gradedAlgebra

theorem Surface.ample_integral_nodal_section_framed_etale_s01 (S : Surface)
    (L : LineBundle S.scheme) (hL : LineBundle.IsAmple S.scheme L) :
    ∃ d : ℕ, 0 < d ∧ ∃ N : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (modulePow S.scheme L.sheaf d),
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
      ∃ y : S.scheme, ∃ U : S.scheme.affineOpens, ∃ hyU : y ∈ U.1,
      ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
      ∃ _ : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ t : Fin 2 → Γ(S.scheme,U.1),
        (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale ∧
        let k := S.structureMap.appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
        let _ : Algebra ℂ Γ(S.scheme, U.1) := (openScalars S.structureMap U.1).toAlgebra
        ∃ v : QuarticIndex (Fin N) → ℂ,
          (∀ x : S.scheme, x ∉ centeredOpen s ↔ x = y) ∧
          IsIntegral (doublePointQuarticIdeal k s hs v).subscheme ∧
          topologicalKrullDim (doublePointQuarticIdeal k s hs v).subscheme = 1 ∧
          InvertiblePullbackIdeal (doublePointQuarticIdeal k s hs v) (𝟙 S.scheme) ∧
          y ∈ (doublePointQuarticIdeal k s hs v).support ∧
          sectionCombination k (doublePointQuartics s) v ≠ 0 ∧
          Smooth (((doublePointQuarticIdeal k s hs v).comap (centeredOpen s).ι).subschemeι ≫
            (centeredOpen s).ι ≫ S.structureMap) ∧
          let f := U.1.topIso.hom (coefficient
            (sectionFrameOn (powerSection (s none) 4) U.1
              (hU.trans (sectionOpen_le_powerSection (s none) 4)))
            (restrictSection U.1.ι (sectionCombination k (doublePointQuartics s) v)))
          ∃ q : (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
            ringKrullDim Γ(S.scheme,U.1) ≤ 2 ∧ (Ideal.span {f}).IsPrime ∧
            f ≠ 0 ∧ q 0 f = 0 ∧
            RingHom.ker (q 0) = (U.2.isoSpec.hom ⟨y,hyU⟩).asIdeal ∧
            ∃ hq : (∀ a, AnalyticAt ℂ (fun z => q z a) 0),
            ∃ u : (ℂ × ℂ) → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
              (∀ᶠ z in 𝓝 0, q z f = u z*z.1*z.2) ∧
              (∃ i : Fin 2 → Fin N, ∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ),
                HasFDerivAt (fun z =>
                  (q z (-affineSectionRatios s U hU (some (i 1))),
                   q z (-affineSectionRatios s U hU (some (i 0)))))
                  (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
              (∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
                (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
                (analyticTaylor q hq).toRingHom) =
                  (U.2.isoSpec.hom ⟨y,hyU⟩).asIdeal^n ∧
                Function.Surjective ((Ideal.Quotient.mk
                  (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
                  (analyticTaylor q hq).toRingHom)) ∧
              Function.Injective (analyticTaylor q hq) ∧
              ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn q V := by
  sorry
end
end MaximalSeshadri.Geometry

end

end OAI
end
