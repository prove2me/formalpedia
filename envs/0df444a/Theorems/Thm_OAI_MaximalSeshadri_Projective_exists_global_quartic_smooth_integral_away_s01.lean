-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_exists_global_quartic_smooth_integral_away_s01
-- name    : OAI.MaximalSeshadri.Projective.exists_global_quartic_smooth_integral_away_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:18:24.140878+00:00
-- url     : https://prove2.me/theorems/1897911e-3768-49b4-8bd6-46d4ad3a2220
-- title:
--   OAI.MaximalSeshadri.Projective.exists_global_quartic_smooth_integral_away_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Projective.exists_global_quartic_smooth_integral_away` of [lean/OAI/AlgebraicGeometry/Seshadri/Projective/QuarticIdealBertini.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/QuarticIdealBertini.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Projective`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.IdealPullback MaximalSeshadri.BertiniIntegral`):
--
--   ```lean
--   theorem exists_global_quartic_smooth_integral_away_s01
--       [CharZero K] [IsAlgClosed K] [Uncountable K] {M : X.Modules}
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
--       ∃ v : Option (Fin n) → K, MvPolynomial.aeval v P ≠ 0 ∧
--         let J := (doublePointQuarticIdeal k s hs (v ∘ e.symm)).comap V.ι
--         IsIntegral J.subscheme ∧ Smooth (J.subschemeι ≫ V.ι ≫ g)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Projective.QuarticIndex` and `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Projective.centeredOpen`, `OAI.MaximalSeshadri.Projective.doublePointQuarticIdeal` and `OAI.MaximalSeshadri.Projective.sectionsMorphism` (definitions bundle `Q223SES009` of this split).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.Surface.ample_quartic_smooth_integral_away_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/QuarticIdealBertini.lean (declaration OAI.MaximalSeshadri.Projective.exists_global_quartic_smooth_integral_away)

import Mathlib
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.IdealPullback MaximalSeshadri.BertiniIntegral
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ τ : Type} [Field K] [Fintype σ] {X : Scheme}

theorem exists_global_quartic_smooth_integral_away_s01
    [CharZero K] [IsAlgClosed K] [Uncountable K] {M : X.Modules}
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
    ∃ v : Option (Fin n) → K, MvPolynomial.aeval v P ≠ 0 ∧
      let J := (doublePointQuarticIdeal k s hs (v ∘ e.symm)).comap V.ι
      IsIntegral J.subscheme ∧ Smooth (J.subschemeι ≫ V.ι ≫ g) := by
  sorry

end
end MaximalSeshadri.Projective
end

end
end

end OAI
end
