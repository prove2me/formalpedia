-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_ProjectiveBertini_exists_smooth_integral_cartier_section_of_local_coordinates_s01
-- name    : OAI.MaximalSeshadri.ProjectiveBertini.exists_smooth_integral_cartier_section_of_local_coordinates_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:19:27.566354+00:00
-- url     : https://prove2.me/theorems/113eb326-ff9c-4196-b80c-9ca25456010d
-- title:
--   OAI.MaximalSeshadri.ProjectiveBertini.exists_smooth_integral_cartier_section_of_local_coordinates_s01 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.ProjectiveBertini.exists_smooth_integral_cartier_section_of_local_coordinates` of [lean/OAI/AlgebraicGeometry/Seshadri/Projective/LocalBertiniSection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/LocalBertiniSection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.ProjectiveBertini`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Projective MaximalSeshadri.BertiniIntegral MaximalSeshadri.Frames`):
--
--   ```lean
--   theorem exists_smooth_integral_cartier_section_of_local_coordinates_s01
--       {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
--       {n : ℕ} (X : Scheme) [IsIntegral X] [CompactSpace X]
--       (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
--       (M : X.Modules) (k : K →+* Γ(X, ⊤))
--       (s : Option (Fin n) → (O X ⟶ M))
--       (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
--       (h : X ⟶ Proj (PolyGrade K (Option (Fin n))))
--       (hh : h = sectionsMorphism k s hs)
--       (hbase : h ≫ projectiveToSpec = g)
--       (hlocal : ∀ x : X, ∃ i : Option (Fin n), ∃ V : X.affineOpens, x ∈ V.1 ∧
--         ∃ φ : PolyChart (R := K) i →+* Γ(X, V.1), Function.Surjective φ ∧
--           Spec.map (CommRingCat.ofHom φ) ≫
--             Proj.awayι (PolyGrade K (Option (Fin n))) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
--               V.2.fromSpec ≫ h)
--       (q : MvPolynomial (Option (Fin n)) K) (hq : q ≠ 0) :
--       ∃ t : Option (Fin n) → K, MvPolynomial.aeval t q ≠ 0 ∧
--         IsIntegral (projectiveHyperplane h t).subscheme ∧
--         Smooth ((projectiveHyperplane h t).subschemeι ≫ g) ∧
--         ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ r : Γ(X, U.1),
--           IsRegular r ∧ (projectiveHyperplane h t).ideal U = Ideal.span {r} ∧
--           ∃ e : M.restrict U.1.ι ≅ O U.1.toScheme,
--             U.1.topIso.hom (coefficient e (restrictSection U.1.ι
--               (sectionCombination k s t))) = r
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.BertiniIntegral.projectiveHyperplane`, `OAI.MaximalSeshadri.Frames.O`, `OAI.MaximalSeshadri.Frames.coefficient`, `OAI.MaximalSeshadri.Projective.PolyChart`, `OAI.MaximalSeshadri.Projective.PolyGrade`, `OAI.MaximalSeshadri.Projective.poly_X_mem` and `OAI.MaximalSeshadri.Projective.projectiveToSpec` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Frames.restrictSection` (definitions bundle `Q223SES004` of this split); `OAI.MaximalSeshadri.Projective.sectionCombination` (definitions bundle `Q223SES006` of this split); `OAI.MaximalSeshadri.Projective.sectionsMorphism` (definitions bundle `Q223SES009` of this split).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Projective.doublePointQuartics_bertini_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/LocalBertiniSection.lean (declaration OAI.MaximalSeshadri.ProjectiveBertini.exists_smooth_integral_cartier_section_of_local_coordinates)

import Mathlib
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.BertiniIntegral MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_smooth_integral_cartier_section_of_local_coordinates_s01
    {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    {n : ℕ} (X : Scheme) [IsIntegral X] [CompactSpace X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (M : X.Modules) (k : K →+* Γ(X, ⊤))
    (s : Option (Fin n) → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (h : X ⟶ Proj (PolyGrade K (Option (Fin n))))
    (hh : h = sectionsMorphism k s hs)
    (hbase : h ≫ projectiveToSpec = g)
    (hlocal : ∀ x : X, ∃ i : Option (Fin n), ∃ V : X.affineOpens, x ∈ V.1 ∧
      ∃ φ : PolyChart (R := K) i →+* Γ(X, V.1), Function.Surjective φ ∧
        Spec.map (CommRingCat.ofHom φ) ≫
          Proj.awayι (PolyGrade K (Option (Fin n))) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
            V.2.fromSpec ≫ h)
    (q : MvPolynomial (Option (Fin n)) K) (hq : q ≠ 0) :
    ∃ t : Option (Fin n) → K, MvPolynomial.aeval t q ≠ 0 ∧
      IsIntegral (projectiveHyperplane h t).subscheme ∧
      Smooth ((projectiveHyperplane h t).subschemeι ≫ g) ∧
      ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ r : Γ(X, U.1),
        IsRegular r ∧ (projectiveHyperplane h t).ideal U = Ideal.span {r} ∧
        ∃ e : M.restrict U.1.ι ≅ O U.1.toScheme,
          U.1.topIso.hom (coefficient e (restrictSection U.1.ι
            (sectionCombination k s t))) = r := by
  sorry

end
end MaximalSeshadri.ProjectiveBertini

end

end
end

end OAI
end
