-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_framedSectionsMorphism_closed_s01
-- name    : OAI.MaximalSeshadri.Projective.framedSectionsMorphism_closed_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:17:11.788207+00:00
-- url     : https://prove2.me/theorems/c4e17c12-2c78-4d73-ae9a-a7f853ab1375
-- title:
--   OAI.MaximalSeshadri.Projective.framedSectionsMorphism_closed_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Projective.framedSectionsMorphism_closed` of [lean/OAI/AlgebraicGeometry/Seshadri/Projective/FramedMaps.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/FramedMaps.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Projective`, with `open CategoryTheory`, `open CategoryTheory.Category CategoryTheory.Functor`, `open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial`, `open scoped AlgebraicGeometry`, `open MaximalSeshadri.Frames`):
--
--   ```lean
--   theorem framedSectionsMorphism_closed_s01
--       [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))]
--       (hU : ∀ i, SectionOpens.isoOpen (s (a i)) = U i)
--       (haff : ∀ i, IsAffine (U i).toScheme)
--       (hgen : ∀ i, Function.Surjective
--         (eval₂Hom ((U i).ι.appTop.hom.comp k)
--           (fun j => coefficient (e i) (restrictSection (U i).ι (s j))))) :
--       IsClosedImmersion (framedSectionsMorphism k s U hc e a hnorm)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` and `OAI.MaximalSeshadri.Frames.coefficient` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Frames.restrictSection` (definitions bundle `Q223SES004` of this split); `OAI.MaximalSeshadri.Projective.framedSectionsMorphism` (definitions bundle `Q223SES007` of this split).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.LineBundle.power_section_embedding_s01` and `OAI.MaximalSeshadri.Geometry.Surface.coprime_embedding_option_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/FramedMaps.lean (declaration OAI.MaximalSeshadri.Projective.framedSectionsMorphism_closed)

import Mathlib
import Definitions.Def_Q223SES007

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ ι : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
  (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
  (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
  (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)

theorem framedSectionsMorphism_closed_s01
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))]
    (hU : ∀ i, SectionOpens.isoOpen (s (a i)) = U i)
    (haff : ∀ i, IsAffine (U i).toScheme)
    (hgen : ∀ i, Function.Surjective
      (eval₂Hom ((U i).ι.appTop.hom.comp k)
        (fun j => coefficient (e i) (restrictSection (U i).ι (s j))))) :
    IsClosedImmersion (framedSectionsMorphism k s U hc e a hnorm) := by
  sorry

end
end MaximalSeshadri.Projective

end
end
end

end OAI
end
