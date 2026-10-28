-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedCurveRigidity_ordinary_coordinate_constant_q68
-- name    : OAI.PiExponent.WeightedCurveRigidity.ordinary_coordinate_constant_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:23:34.189772+00:00
-- url     : https://prove2.me/theorems/6b7a2cac-fde7-4559-8588-b9dee2124095
-- title:
--   OAI.PiExponent.WeightedCurveRigidity.ordinary_coordinate_constant_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.WeightedCurveRigidity.ordinary_coordinate_constant` of [lean/OAI/NumberTheory/PiExponent/Geometry/WeightedCurveRigidity.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/WeightedCurveRigidity.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.WeightedCurveRigidity`, with `open scoped BigOperators`, `open PiExponentApprox PersistentWeightComparison`):
--
--   ```lean
--   theorem ordinary_coordinate_constant_q68 {m n : ℕ} (hn : n ≤ m + 2)
--       (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
--       (cost : Fin n → ℝ) (hcost : ∀ i, 0 < cost i)
--       (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
--       (hrect : UniformRectangles n cost (sigma / ((m : ℝ) + 2)) N)
--       (F : OrdinaryDerivatives.Polynomial n) (hF0 : F ≠ 0)
--       (hF : WeightedSliceDegree.SupportBound (fun i => (rho i : ℝ)) N F)
--       (d : ℕ) (hd : d ≤ m)
--       (P : Ideal (OrdinaryDerivatives.Polynomial n)) (hP : P.IsPrime) (hheight : P.height ≤ d)
--       (hvanish : ∀ word : List (Fin n), DerivativeIdeals.wordCost cost word ≤ sigma * N →
--         OrdinaryDerivatives.word n word F ∈ P)
--       (hseparated : ∀ A B : Finset (Fin n), A.card = B.card →
--         ∀ i, i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
--         comparisonConstant m sigma * (∏ j ∈ B, cost j) < ∏ j ∈ A, (rho j : ℝ)) :
--       ∃ i : Fin n, ∃ c : ℂ, MvPolynomial.X i - MvPolynomial.C c ∈ P
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.WeightedSliceDegree.SupportBound` (definitions bundle `OAIQ068A006` of this split); `OAI.PiExponent.DerivativeIdeals.wordCost` (definitions bundle `OAIQ068A007` of this split); `OAI.PiExponent.OrdinaryDerivatives.Polynomial`, `OAI.PiExponent.PersistentWeightComparison.UniformRectangles` and `OAI.PiExponent.PersistentWeightComparison.comparisonConstant` (definitions bundle `OAIQ068A008` of this split); `OAI.PiExponent.OrdinaryDerivatives.word` (definitions bundle `OAIQ068A017` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.CurveInequality.weighted_curve_inequality_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/WeightedCurveRigidity.lean (declaration OAI.PiExponent.WeightedCurveRigidity.ordinary_coordinate_constant)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A017

section

attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.WeightedCurveRigidity

open scoped BigOperators
open PiExponentApprox PersistentWeightComparison

theorem ordinary_coordinate_constant_q68 {m n : ℕ} (hn : n ≤ m + 2)
    (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin n → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles n cost (sigma / ((m : ℝ) + 2)) N)
    (F : OrdinaryDerivatives.Polynomial n) (hF0 : F ≠ 0)
    (hF : WeightedSliceDegree.SupportBound (fun i => (rho i : ℝ)) N F)
    (d : ℕ) (hd : d ≤ m)
    (P : Ideal (OrdinaryDerivatives.Polynomial n)) (hP : P.IsPrime) (hheight : P.height ≤ d)
    (hvanish : ∀ word : List (Fin n), DerivativeIdeals.wordCost cost word ≤ sigma * N →
      OrdinaryDerivatives.word n word F ∈ P)
    (hseparated : ∀ A B : Finset (Fin n), A.card = B.card →
      ∀ i, i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, cost j) < ∏ j ∈ A, (rho j : ℝ)) :
    ∃ i : Fin n, ∃ c : ℂ, MvPolynomial.X i - MvPolynomial.C c ∈ P := by
  sorry

end PiExponent.WeightedCurveRigidity
end

end OAI
end
