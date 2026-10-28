-- Prove2me | Theorems.Thm_OAI_PiExponent_BlowupJetSurjectivity_eventual_blowup_jetRestriction_surjective_of_section_comparison_q68
-- name    : OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_section_comparison_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:46:45.362322+00:00
-- url     : https://prove2.me/theorems/2ab1233e-5ad5-4d97-8993-b4d9f94fa936
-- title:
--   OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_section_comparison_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_section_comparison` of [lean/OAI/NumberTheory/PiExponent/Ampleness/GlobalBlowupJetSurjectivity.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/GlobalBlowupJetSurjectivity.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.BlowupJetSurjectivity`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open PiExponentSeshadri.Geometry`, `open PiExponent.GeometrySupport`):
--
--   ```lean
--   theorem eventual_blowup_jetRestriction_surjective_of_section_comparison_q68
--       (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
--       (I : X.IdealSheafData) (A : LineBundle X)
--       (hample : LineBundle.IsAmple _ (blowupBundle I A))
--       {J : Type} (U : J → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
--       (hcover : (⨆ i, U i) = ⊤)
--       (hcomparison : ∃ N, ∀ n, N ≤ n → Nonempty
--         (CechH1Transfer.SectionComparison U
--           (fun i => PiExponentSeshadri.BlowupGluing.projection I ⁻¹ᵁ U i)
--           (twistedIdeal I A n)
--           (modulePow (PiExponentSeshadri.BlowupGluing.scheme I) (blowupBundle I A).sheaf n))) :
--       ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.Geometry.LineBundle` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponentSeshadri.Geometry.modulePow` and `OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor` (definitions bundle `OAIQ068A012` of this split); `OAI.PiExponentSeshadri.Geometry.GlobalSections` (definitions bundle `OAIQ068A013` of this split); `OAI.PiExponent.BlowupJetSurjectivity.jetQuotient` (definitions bundle `OAIQ068A017` of this split); `OAI.PiExponentSeshadri.BlowupGluing.projection` and `OAI.PiExponentSeshadri.BlowupGluing.scheme` (definitions bundle `OAIQ068A020` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple` (definitions bundle `OAIQ068A021` of this split); `OAI.PiExponent.BlowupJetSurjectivity.jetRestriction`, `OAI.PiExponent.BlowupJetSurjectivity.twistedIdeal` and `OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison` (definitions bundle `OAIQ068A032` of this split); `OAI.PiExponent.BlowupJetSurjectivity.blowupBundle` (definitions bundle `OAIQ068A038` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_affine_recovery_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/GlobalBlowupJetSurjectivity.lean (declaration OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_section_comparison)

import Mathlib
import Definitions.Def_OAIQ068A038

section

attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem eventual_blowup_jetRestriction_surjective_of_section_comparison_q68
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (A : LineBundle X)
    (hample : LineBundle.IsAmple _ (blowupBundle I A))
    {J : Type} (U : J → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤)
    (hcomparison : ∃ N, ∀ n, N ≤ n → Nonempty
      (CechH1Transfer.SectionComparison U
        (fun i => PiExponentSeshadri.BlowupGluing.projection I ⁻¹ᵁ U i)
        (twistedIdeal I A n)
        (modulePow (PiExponentSeshadri.BlowupGluing.scheme I) (blowupBundle I A).sheaf n))) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  sorry

end
end PiExponent.BlowupJetSurjectivity

end OAI
end
