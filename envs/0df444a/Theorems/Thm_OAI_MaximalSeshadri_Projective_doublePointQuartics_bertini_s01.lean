-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_doublePointQuartics_bertini_s01
-- name    : OAI.MaximalSeshadri.Projective.doublePointQuartics_bertini_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:08:16.421201+00:00
-- url     : https://prove2.me/theorems/7db3d73a-a0a4-4928-8d79-d7cfb27fc7c3
-- title:
--   OAI.MaximalSeshadri.Projective.doublePointQuartics_bertini_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Projective.doublePointQuartics_bertini` of [lean/OAI/AlgebraicGeometry/Seshadri/Projective/QuarticBertini.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/QuarticBertini.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Projective`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial`, `open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.BertiniIntegral`):
--
--   ```lean
--   theorem doublePointQuartics_bertini_s01 {X : Scheme} {M : X.Modules}
--       (g : X ⟶ Spec (CommRingCat.of K))
--       (s : Option σ → (O X ⟶ M))
--       (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
--       [IsClosedImmersion (sectionsMorphism
--         (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
--       {n : ℕ} (e : Option (Fin n) ≃ QuarticIndex σ)
--       [IsIntegral (centeredOpen s).toScheme] [CompactSpace (centeredOpen s)]
--       [SmoothOfRelativeDimension 2 ((centeredOpen s).ι ≫ g)]
--       (P : MvPolynomial (Option (Fin n)) K) (hP : P ≠ 0) :
--       let k := g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
--       let V := centeredOpen s
--       let t (j : Option σ) := restrictSection V.ι (s j)
--       let q := (doublePointQuartics t) ∘ e
--       let hq := sections_cover_reindex _ (doublePointQuartics_cover t (restricted_centered_cover s)) e
--       let h := sectionsMorphism (V.ι.appTop.hom.comp k) q hq
--       ∃ v : Option (Fin n) → K, MvPolynomial.aeval v P ≠ 0 ∧
--         IsIntegral (projectiveHyperplane h v).subscheme ∧
--         Smooth ((projectiveHyperplane h v).subschemeι ≫ V.ι ≫ g) ∧
--         ∀ x : V, ∃ U : V.toScheme.affineOpens, x ∈ U.1 ∧
--           ∃ f : Γ(V.toScheme, U.1), IsRegular f ∧
--             (projectiveHyperplane h v).ideal U = Ideal.span {f} ∧
--             ∃ b : (modulePow V.toScheme (M.restrict V.ι) 4).restrict U.1.ι ≅ O U.1.toScheme,
--               U.1.topIso.hom (coefficient b (restrictSection U.1.ι
--                 (sectionCombination (V.ι.appTop.hom.comp k) q v))) = f
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.BertiniIntegral.projectiveHyperplane`, `OAI.MaximalSeshadri.Frames.O` and `OAI.MaximalSeshadri.Frames.coefficient` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Projective.QuarticIndex` and `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Frames.restrictSection` (definitions bundle `Q223SES004` of this split); `OAI.MaximalSeshadri.Projective.sectionCombination` (definitions bundle `Q223SES006` of this split); `OAI.MaximalSeshadri.Projective.doublePointQuartics` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Projective.centeredOpen`, `OAI.MaximalSeshadri.Projective.doublePointQuartics_cover`, `OAI.MaximalSeshadri.Projective.restricted_centered_cover`, `OAI.MaximalSeshadri.Projective.sectionsMorphism` and `OAI.MaximalSeshadri.Projective.sections_cover_reindex` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.modulePow` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Projective.exists_global_quartic_smooth_integral_away_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/QuarticBertini.lean (declaration OAI.MaximalSeshadri.Projective.doublePointQuartics_bertini)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.BertiniIntegral
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]

theorem doublePointQuartics_bertini_s01 {X : Scheme} {M : X.Modules}
    (g : X ⟶ Spec (CommRingCat.of K))
    (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
    {n : ℕ} (e : Option (Fin n) ≃ QuarticIndex σ)
    [IsIntegral (centeredOpen s).toScheme] [CompactSpace (centeredOpen s)]
    [SmoothOfRelativeDimension 2 ((centeredOpen s).ι ≫ g)]
    (P : MvPolynomial (Option (Fin n)) K) (hP : P ≠ 0) :
    let k := g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    let V := centeredOpen s
    let t (j : Option σ) := restrictSection V.ι (s j)
    let q := (doublePointQuartics t) ∘ e
    let hq := sections_cover_reindex _ (doublePointQuartics_cover t (restricted_centered_cover s)) e
    let h := sectionsMorphism (V.ι.appTop.hom.comp k) q hq
    ∃ v : Option (Fin n) → K, MvPolynomial.aeval v P ≠ 0 ∧
      IsIntegral (projectiveHyperplane h v).subscheme ∧
      Smooth ((projectiveHyperplane h v).subschemeι ≫ V.ι ≫ g) ∧
      ∀ x : V, ∃ U : V.toScheme.affineOpens, x ∈ U.1 ∧
        ∃ f : Γ(V.toScheme, U.1), IsRegular f ∧
          (projectiveHyperplane h v).ideal U = Ideal.span {f} ∧
          ∃ b : (modulePow V.toScheme (M.restrict V.ι) 4).restrict U.1.ι ≅ O U.1.toScheme,
            U.1.topIso.hom (coefficient b (restrictSection U.1.ι
              (sectionCombination (V.ι.appTop.hom.comp k) q v))) = f := by
  sorry

end
end MaximalSeshadri.Projective
end

end
end

end OAI
end
