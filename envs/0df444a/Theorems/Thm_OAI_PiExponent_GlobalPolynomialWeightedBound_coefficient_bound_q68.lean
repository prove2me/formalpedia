-- Prove2me | Theorems.Thm_OAI_PiExponent_GlobalPolynomialWeightedBound_coefficient_bound_q68
-- name    : OAI.PiExponent.GlobalPolynomialWeightedBound.coefficient_bound_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:51:16.826674+00:00
-- url     : https://prove2.me/theorems/4e16d153-6b35-4acc-88d7-233ab407aab0
-- title:
--   OAI.PiExponent.GlobalPolynomialWeightedBound.coefficient_bound_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.GlobalPolynomialWeightedBound.coefficient_bound` of [lean/OAI/NumberTheory/PiExponent/Polynomials/GlobalPolynomialWeightedBound.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Polynomials/GlobalPolynomialWeightedBound.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.GlobalPolynomialWeightedBound`, with `open AlgebraicGeometry CategoryTheory`, `open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames`, `open PiExponent.WeightedSliceDegree PiExponent.AffineJetCoefficientInterface`):
--
--   ```lean
--   theorem coefficient_bound_q68 {X Y : Scheme.{0}} {K ι B : Type}
--       [Field K] [CommRing B] (L : LineBundle Y) (f : X ⟶ Y)
--       (φ : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion φ]
--       (V : Y.Opens) (g : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ V.toScheme)
--       (hg : φ ≫ f = g ≫ V.ι) (n : ℕ)
--       (e : (modulePow Y L.sheaf n).restrict V.ι ≅ structureSheaf V.toScheme)
--       (E : Γ(Y,V) ≃+* B) (P : (structureSheaf Y ⟶ modulePow Y L.sheaf n) → B)
--       (hP : GlobalPolynomialCoefficientLaw.CoefficientLaw V e E P)
--       (ev : B →+* MvPolynomial ι K)
--       (hev : ∀ q, (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι K))).hom
--         (g.appTop (V.topIso.inv (E.symm q))) = ev q)
--       (ρ : ι → ℝ) (r : ℝ) (eTarget : Frame φ (L.pullback f)) (s : Sections L n)
--       (hbound : SupportBound ρ r (ev (P s))) :
--       SupportBound ρ r (AffineJetCoefficientInterface.coefficient φ (L.pullback f) n eTarget
--         (pullbackPowerSection L f n s))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.Geometry.LineBundle` and `OAI.PiExponentSeshadri.Geometry.structureSheaf` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponent.WeightedSliceDegree.SupportBound` (definitions bundle `OAIQ068A006` of this split); `OAI.PiExponentSeshadri.Geometry.modulePow` and `OAI.PiExponentSeshadri.Geometry.LineBundle.pullback` (definitions bundle `OAIQ068A012` of this split); `OAI.PiExponentSeshadri.Geometry.pullbackPowerSection` (definitions bundle `OAIQ068A028` of this split); `OAI.PiExponent.GlobalPolynomialCoefficientLaw.CoefficientLaw` (definitions bundle `OAIQ068A033` of this split); `OAI.PiExponent.AffineJetCoefficientInterface.Frame`, `OAI.PiExponent.AffineJetCoefficientInterface.Sections` and `OAI.PiExponent.AffineJetCoefficientInterface.coefficient` (definitions bundle `OAIQ068A044` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.WeightedPullbackDegree.pullback_supportBound_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Polynomials/GlobalPolynomialWeightedBound.lean (declaration OAI.PiExponent.GlobalPolynomialWeightedBound.coefficient_bound)

import Mathlib
import Definitions.Def_OAIQ068A044

section

attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.GlobalPolynomialWeightedBound
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.WeightedSliceDegree PiExponent.AffineJetCoefficientInterface

theorem coefficient_bound_q68 {X Y : Scheme.{0}} {K ι B : Type}
    [Field K] [CommRing B] (L : LineBundle Y) (f : X ⟶ Y)
    (φ : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion φ]
    (V : Y.Opens) (g : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ V.toScheme)
    (hg : φ ≫ f = g ≫ V.ι) (n : ℕ)
    (e : (modulePow Y L.sheaf n).restrict V.ι ≅ structureSheaf V.toScheme)
    (E : Γ(Y,V) ≃+* B) (P : (structureSheaf Y ⟶ modulePow Y L.sheaf n) → B)
    (hP : GlobalPolynomialCoefficientLaw.CoefficientLaw V e E P)
    (ev : B →+* MvPolynomial ι K)
    (hev : ∀ q, (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι K))).hom
      (g.appTop (V.topIso.inv (E.symm q))) = ev q)
    (ρ : ι → ℝ) (r : ℝ) (eTarget : Frame φ (L.pullback f)) (s : Sections L n)
    (hbound : SupportBound ρ r (ev (P s))) :
    SupportBound ρ r (AffineJetCoefficientInterface.coefficient φ (L.pullback f) n eTarget
      (pullbackPowerSection L f n s)) := by
  sorry

end PiExponent.GlobalPolynomialWeightedBound
end

end OAI
end
