-- Prove2me | Theorems.Thm_OAI_PiExponent_CurveDerivativeVanishing_logarithmic_words_vanish_q68
-- name    : OAI.PiExponent.CurveDerivativeVanishing.logarithmic_words_vanish_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:35:48.679607+00:00
-- url     : https://prove2.me/theorems/fa7f2b04-2f12-489d-b225-8bd2ca92d29e
-- title:
--   OAI.PiExponent.CurveDerivativeVanishing.logarithmic_words_vanish_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.CurveDerivativeVanishing.logarithmic_words_vanish` of [lean/OAI/NumberTheory/PiExponent/Cohomology/CurveDerivativeVanishing.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Cohomology/CurveDerivativeVanishing.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.CurveDerivativeVanishing`, with `open scoped BigOperators`, `open PiExponentApprox CurveValuationCenter PlaceValuationRing CurveContactFamily`):
--
--   ```lean
--   theorem logarithmic_words_vanish_q68
--       {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
--       (hres : ∀ p : NormalizedPlace ℂ E,
--         Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
--       (hfinite : ∀ f : E, Transcendental ℂ f →
--         FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
--       (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
--       (hz : ∃ i, Transcendental ℂ (z i))
--       (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
--       (sigma : ℚ) (hsigma : 0 < sigma) (N : ℕ) (hN : 0 < N)
--       (F : FramePolynomial m)
--       (hF : HasWeightedDegreeLE (fun i => (w i : ℝ)) N F)
--       (hjet : ∀ j, FormalLogJet.formalJet (c j) F ∈
--         JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) ((1+3*sigma)*N))
--       (hexcess : CurveContactSum.weightedDegree hfinite z w <
--         (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz, (contact hres hfinite z c hz v p : ℝ)) :
--       ∀ word : List (Fin (m+1)),
--         frameWordCost (fun i => (v i : ℝ)) word ≤ (sigma : ℝ)*N →
--           MvPolynomial.aeval z (polynomialFrameWord m word F) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.CurveValuationCenter.NormalizedPlace` (definitions bundle `OAIQ068A002` of this split); `OAI.PiExponentApprox.FramePolynomial` (definitions bundle `OAIQ068A006` of this split); `OAI.PiExponentApprox.frameWordCost` (definitions bundle `OAIQ068A007` of this split); `OAI.PiExponent.JetGeometry.rationalWeightedIdeal` (definitions bundle `OAIQ068A008` of this split); `OAI.PiExponentApprox.HasWeightedDegreeLE` (definitions bundle `OAIQ068A009` of this split); `OAI.PiExponent.PlaceValuationRing.constantsAlgebra` and `OAI.PiExponent.PlaceValuationRing.ring` (definitions bundle `OAIQ068A014` of this split); `OAI.PiExponentApprox.polynomialFrameWord` and `OAI.PiExponent.FormalLogJet.formalJet` (definitions bundle `OAIQ068A017` of this split); `OAI.PiExponent.CurveContactFamily.places` (definitions bundle `OAIQ068A022` of this split); `OAI.PiExponent.CurveContactFamily.contact` and `OAI.PiExponent.CurveContactSum.weightedDegree` (definitions bundle `OAIQ068A029` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.CurveInequality.excess_implies_zeroth_eq_one_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Cohomology/CurveDerivativeVanishing.lean (declaration OAI.PiExponent.CurveDerivativeVanishing.logarithmic_words_vanish)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A009
import Definitions.Def_OAIQ068A017
import Definitions.Def_OAIQ068A029

section

attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveDerivativeVanishing

open PiExponentApprox CurveValuationCenter PlaceValuationRing CurveContactFamily

theorem logarithmic_words_vanish_q68
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma) (N : ℕ) (hN : 0 < N)
    (F : FramePolynomial m)
    (hF : HasWeightedDegreeLE (fun i => (w i : ℝ)) N F)
    (hjet : ∀ j, FormalLogJet.formalJet (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) ((1+3*sigma)*N))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz, (contact hres hfinite z c hz v p : ℝ)) :
    ∀ word : List (Fin (m+1)),
      frameWordCost (fun i => (v i : ℝ)) word ≤ (sigma : ℝ)*N →
        MvPolynomial.aeval z (polynomialFrameWord m word F) = 0 := by
  sorry

end PiExponent.CurveDerivativeVanishing
end

end OAI
end
