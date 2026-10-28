-- Prove2me | Theorems.Thm_OAI_PiExponent_TransverseSliceComparison_comparison_of_normal_basis_q68
-- name    : OAI.PiExponent.TransverseSliceComparison.comparison_of_normal_basis_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:22:12.728351+00:00
-- url     : https://prove2.me/theorems/42c648c2-c9fc-4b07-a547-b64ad0ef73a7
-- title:
--   OAI.PiExponent.TransverseSliceComparison.comparison_of_normal_basis_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.TransverseSliceComparison.comparison_of_normal_basis` of [lean/OAI/NumberTheory/PiExponent/Jets/TransverseSliceComparison.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Jets/TransverseSliceComparison.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.TransverseSliceComparison`, with `open scoped BigOperators`, `open PiExponentApprox NormalBasisRigidity`, `open WeightedSliceDegree`):
--
--   ```lean
--   theorem comparison_of_normal_basis_q68 {m : ℕ}
--       (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
--       (hy : primeResidueMap Q (MvPolynomial.X (0 : Fin (m + 1))) ≠ 0)
--       (A : Finset (Fin (m + 1))) (hk : 0 < A.card)
--       (hA : IsNormalBasis (K := Q.ResidueField)
--         (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
--           (Pi.basisFun Q.ResidueField _ i)) A)
--       (B : Fin A.card → Fin (m + 1))
--       (hB : LinearIndependent Q.ResidueField
--         (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
--           (frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) hy (B j))))
--       {J : Type*} (f : J → FramePolynomial m)
--       (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
--       (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
--       (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
--       (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
--       (hdegree : ∀ j, ∀ d ∈ (f j).support,
--         (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N)
--       (hn : ∀ i, 2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i)
--       (hvanish : ∀ p ∈ Ideal.span (Set.range f), ∀ word : List (Fin (m + 1)),
--         frameWordCost cost word ≤ epsilon * N → polynomialFrameWord m word p ∈ Q) :
--       (∏ i ∈ A, (rho i : ℝ)) ≤
--         (A.card : ℝ) ^ A.card * (∏ i, cost (B i)) / epsilon ^ A.card
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentApprox.FramePolynomial` (definitions bundle `OAIQ068A006` of this split); `OAI.PiExponent.polynomialTangent`, `OAI.PiExponent.primeResidueMap`, `OAI.PiExponentApprox.frameWordCost`, `OAI.PiExponent.NormalBasisRigidity.IsNormalBasis` and `OAI.PiExponent.NormalBasisRigidity.frameBasis` (definitions bundle `OAIQ068A007` of this split); `OAI.PiExponent.rectangularCutoff` (definitions bundle `OAIQ068A008` of this split); `OAI.PiExponentApprox.polynomialFrameWord` (definitions bundle `OAIQ068A017` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.CurveInequality.excess_implies_zeroth_eq_one_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Jets/TransverseSliceComparison.lean (declaration OAI.PiExponent.TransverseSliceComparison.comparison_of_normal_basis)

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
namespace PiExponent.TransverseSliceComparison

open scoped BigOperators
open PiExponentApprox NormalBasisRigidity
open WeightedSliceDegree

theorem comparison_of_normal_basis_q68 {m : ℕ}
    (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hy : primeResidueMap Q (MvPolynomial.X (0 : Fin (m + 1))) ≠ 0)
    (A : Finset (Fin (m + 1))) (hk : 0 < A.card)
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ i)) A)
    (B : Fin A.card → Fin (m + 1))
    (hB : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) hy (B j))))
    {J : Type*} (f : J → FramePolynomial m)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N)
    (hn : ∀ i, 2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i)
    (hvanish : ∀ p ∈ Ideal.span (Set.range f), ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ epsilon * N → polynomialFrameWord m word p ∈ Q) :
    (∏ i ∈ A, (rho i : ℝ)) ≤
      (A.card : ℝ) ^ A.card * (∏ i, cost (B i)) / epsilon ^ A.card := by
  sorry

end PiExponent.TransverseSliceComparison
end

end OAI
end
