-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_ample_quartic_integral_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.ample_quartic_integral_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:07:11.37621+00:00
-- url     : https://prove2.me/theorems/b5671cd7-2d0a-4d78-89a5-c0dd246fed78
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.ample_quartic_integral_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.ample_quartic_integral` of [lean/OAI/AlgebraicGeometry/Seshadri/Projective/GlobalIntegralQuartic.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/GlobalIntegralQuartic.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini`):
--
--   ```lean
--   theorem Surface.ample_quartic_integral_s01 (S : Surface)
--       (L : LineBundle S.scheme) (hL : LineBundle.IsAmple S.scheme L) :
--       ∃ d : ℕ, 0 < d ∧ ∃ N n : ℕ,
--         ∃ s : Option (Fin N) → GlobalSections S.scheme (modulePow S.scheme L.sheaf d),
--         ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
--         ∃ e : Option (Fin n) ≃ QuarticIndex (Fin N), ∃ y : S.scheme,
--           (∀ x : S.scheme, x ∉ centeredOpen s ↔ x = y) ∧
--           IsClosedImmersion (sectionsMorphism
--             (S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) s hs) ∧
--           ∀ P : MvPolynomial (Option (Fin n)) ℂ, P ≠ 0 →
--             ∃ v : Option (Fin n) → ℂ, MvPolynomial.aeval v P ≠ 0 ∧
--               let k := S.structureMap.appTop.hom.comp
--                 (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
--               let V := centeredOpen s
--               let J := doublePointQuarticIdeal k s hs (v ∘ e.symm)
--               IsIntegral J.subscheme ∧
--                 Smooth ((J.comap V.ι).subschemeι ≫ V.ι ≫ S.structureMap)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Projective.QuarticIndex` and `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Projective.centeredOpen`, `OAI.MaximalSeshadri.Projective.doublePointQuarticIdeal` and `OAI.MaximalSeshadri.Projective.sectionsMorphism` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.GlobalSections`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.modulePow`, `OAI.MaximalSeshadri.Geometry.structureSheaf` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/GlobalIntegralQuartic.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.ample_quartic_integral)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini

attribute [local instance] MvPolynomial.gradedAlgebra

theorem Surface.ample_quartic_integral_s01 (S : Surface)
    (L : LineBundle S.scheme) (hL : LineBundle.IsAmple S.scheme L) :
    ∃ d : ℕ, 0 < d ∧ ∃ N n : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (modulePow S.scheme L.sheaf d),
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
      ∃ e : Option (Fin n) ≃ QuarticIndex (Fin N), ∃ y : S.scheme,
        (∀ x : S.scheme, x ∉ centeredOpen s ↔ x = y) ∧
        IsClosedImmersion (sectionsMorphism
          (S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) s hs) ∧
        ∀ P : MvPolynomial (Option (Fin n)) ℂ, P ≠ 0 →
          ∃ v : Option (Fin n) → ℂ, MvPolynomial.aeval v P ≠ 0 ∧
            let k := S.structureMap.appTop.hom.comp
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
            let V := centeredOpen s
            let J := doublePointQuarticIdeal k s hs (v ∘ e.symm)
            IsIntegral J.subscheme ∧
              Smooth ((J.comap V.ι).subschemeι ≫ V.ι ≫ S.structureMap) := by
  sorry

end
end MaximalSeshadri.Geometry
end

end
end

end OAI
end
