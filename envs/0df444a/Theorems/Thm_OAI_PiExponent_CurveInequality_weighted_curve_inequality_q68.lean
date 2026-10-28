-- Prove2me | Theorems.Thm_OAI_PiExponent_CurveInequality_weighted_curve_inequality_q68
-- name    : OAI.PiExponent.CurveInequality.weighted_curve_inequality_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:48:29.854436+00:00
-- url     : https://prove2.me/theorems/a21a28e0-f60c-4133-89fb-9e9c79a55859
-- title:
--   OAI.PiExponent.CurveInequality.weighted_curve_inequality_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.CurveInequality.weighted_curve_inequality` of [lean/OAI/NumberTheory/PiExponent/Geometry/CurveInequalityIntrinsic.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/CurveInequalityIntrinsic.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.CurveInequality`, with `open scoped BigOperators`, `open CurveValuationCenter PlaceValuationRing CurveContactFamily PersistentWeightComparison`):
--
--   ```lean
--   theorem weighted_curve_inequality_q68 {m K : ℕ}
--       (y : E) (x : Fin m → E) (c : Fin K → Fin m → ℂ)
--       (hc : ∀ i, Function.Injective (fun j => c j i))
--       (hgen : IntermediateField.adjoin ℂ
--         (Set.range (Fin.cases y x : Fin (m+1) → E)) = ⊤)
--       (htrdeg : Algebra.trdeg ℂ E = 1)
--       (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
--       (sigma : ℚ) (hsigma : 0 < sigma)
--       (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
--         (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
--       (hfibrevol : (K : ℝ) * (1+3*(sigma : ℝ))^m *
--         (∏ i : Fin m, (w i.succ : ℝ)) / (∏ i : Fin m, (v i.succ : ℝ)) < 1)
--       (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
--         ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
--         (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
--         comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
--       (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ : ℝ) < v i.succ) :
--       let hres := PlaceLocalRing.residue_integral htrdeg.le
--       let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
--       let z : Fin (m+1) → E := Fin.cases y x
--       let hz := nonconstant_coordinates z hgen htrdeg
--       (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz,
--         (contact hres hfinite z c hz v p : ℝ) ≤
--           CurveContactSum.weightedDegree hfinite z w
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.CurveValuationCenter.NormalizedPlace` (definitions bundle `OAIQ068A002` of this split); `OAI.PiExponent.CurveInequality.nonconstant_coordinates` and `OAI.PiExponent.CurveParameterFinite.finite_over_every_parameter` (definitions bundle `OAIQ068A003` of this split); `OAI.PiExponent.PersistentWeightComparison.comparisonConstant` (definitions bundle `OAIQ068A008` of this split); `OAI.PiExponent.PlaceValuationRing.constantsAlgebra` and `OAI.PiExponent.PlaceValuationRing.ring` (definitions bundle `OAIQ068A014` of this split); `OAI.PiExponent.CurveContactFamily.places` (definitions bundle `OAIQ068A022` of this split); `OAI.PiExponent.CurveContactFamily.contact` and `OAI.PiExponent.CurveContactSum.weightedDegree` (definitions bundle `OAIQ068A029` of this split); `OAI.PiExponent.PlaceLocalRing.residue_integral` (definitions bundle `OAIQ068A040` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.AdmissibleBlowupGeometry.uniform_curve_margin_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/CurveInequalityIntrinsic.lean (declaration OAI.PiExponent.CurveInequality.weighted_curve_inequality)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A040

section

attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveInequality

open CurveValuationCenter PlaceValuationRing CurveContactFamily PersistentWeightComparison

variable {E : Type*} [Field E] [Algebra ℂ E]

variable [Algebra.EssFiniteType ℂ E]

theorem weighted_curve_inequality_q68 {m K : ℕ}
    (y : E) (x : Fin m → E) (c : Fin K → Fin m → ℂ)
    (hc : ∀ i, Function.Injective (fun j => c j i))
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hfibrevol : (K : ℝ) * (1+3*(sigma : ℝ))^m *
      (∏ i : Fin m, (w i.succ : ℝ)) / (∏ i : Fin m, (v i.succ : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ : ℝ) < v i.succ) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let z : Fin (m+1) → E := Fin.cases y x
    let hz := nonconstant_coordinates z hgen htrdeg
    (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz,
      (contact hres hfinite z c hz v p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z w := by
  sorry

end PiExponent.CurveInequality
end

end OAI
end
