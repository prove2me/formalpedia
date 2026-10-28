-- Prove2me | Theorems.Thm_OAI_PiExponent_CurveInequality_excess_implies_zeroth_eq_one_q68
-- name    : OAI.PiExponent.CurveInequality.excess_implies_zeroth_eq_one_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:39:25.689395+00:00
-- url     : https://prove2.me/theorems/49c0b77b-d870-48ae-982c-c2b20f7ef69f
-- title:
--   OAI.PiExponent.CurveInequality.excess_implies_zeroth_eq_one_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.CurveInequality.excess_implies_zeroth_eq_one` of [lean/OAI/NumberTheory/PiExponent/Geometry/CurveInequality.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/CurveInequality.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.CurveInequality`, with `open scoped BigOperators`, `open Filter Topology`, `open PiExponentApprox CurveValuationCenter PlaceValuationRing CurveContactFamily`, `open PersistentWeightComparison`):
--
--   ```lean
--   theorem excess_implies_zeroth_eq_one_q68
--       {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
--       (hres : ∀ p : NormalizedPlace ℂ E,
--         Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
--       (hfinite : ∀ f : E, Transcendental ℂ f →
--         FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
--       (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
--       (hz : ∃ i, Transcendental ℂ (z i))
--       (hheight : (CurveFieldRigidity.coordinateKernel z).height ≤ m)
--       (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
--       (sigma : ℚ) (hsigma : 0 < sigma)
--       (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
--         (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
--       (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
--         ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
--         (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
--         comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
--       (hexcess : CurveContactSum.weightedDegree hfinite z w <
--         (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz, (contact hres hfinite z c hz v p : ℝ)) :
--       z 0 = 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.CurveValuationCenter.NormalizedPlace` (definitions bundle `OAIQ068A002` of this split); `OAI.PiExponent.CurveFieldRigidity.coordinateKernel` (definitions bundle `OAIQ068A007` of this split); `OAI.PiExponent.PersistentWeightComparison.comparisonConstant` (definitions bundle `OAIQ068A008` of this split); `OAI.PiExponent.PlaceValuationRing.constantsAlgebra` and `OAI.PiExponent.PlaceValuationRing.ring` (definitions bundle `OAIQ068A014` of this split); `OAI.PiExponent.CurveContactFamily.places` (definitions bundle `OAIQ068A022` of this split); `OAI.PiExponent.CurveContactFamily.contact` and `OAI.PiExponent.CurveContactSum.weightedDegree` (definitions bundle `OAIQ068A029` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.CurveInequality.weighted_curve_inequality_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/CurveInequality.lean (declaration OAI.PiExponent.CurveInequality.excess_implies_zeroth_eq_one)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A007
import Definitions.Def_OAIQ068A008
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
open Filter Topology
namespace PiExponent.CurveInequality

open PiExponentApprox CurveValuationCenter PlaceValuationRing CurveContactFamily
open PersistentWeightComparison

theorem excess_implies_zeroth_eq_one_q68
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hheight : (CurveFieldRigidity.coordinateKernel z).height ≤ m)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz, (contact hres hfinite z c hz v p : ℝ)) :
    z 0 = 1 := by
  sorry

end PiExponent.CurveInequality
end

end OAI
end
