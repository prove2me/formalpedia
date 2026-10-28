-- Prove2me | Theorems.Thm_OAI_PiExponent_CoordinateSliceComparison_length_eq_sliceFamily_of_normalBasis_q68
-- name    : OAI.PiExponent.CoordinateSliceComparison.length_eq_sliceFamily_of_normalBasis_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:16:57.845378+00:00
-- url     : https://prove2.me/theorems/474b1854-01ec-41ce-b307-97421f5c1b63
-- title:
--   OAI.PiExponent.CoordinateSliceComparison.length_eq_sliceFamily_of_normalBasis_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.CoordinateSliceComparison.length_eq_sliceFamily_of_normalBasis` of [lean/OAI/NumberTheory/PiExponent/Approximation/CoordinateSliceComparison.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Approximation/CoordinateSliceComparison.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.CoordinateSliceComparison`, with `open PiExponentJets.PolynomialLocalResidueResolution`, `open CoordinateFiniteSlice`):
--
--   ```lean
--   theorem length_eq_sliceFamily_of_normalBasis_q68 [CharZero K]
--       (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
--       (hA : NormalBasisRigidity.IsNormalBasis (K := Q.ResidueField)
--         (fun i => (polynomialTangent
--           (IsScalarTower.toAlgHom K (MvPolynomial ι K) Q.ResidueField) Q).mkQ
--           (Pi.basisFun Q.ResidueField ι i)) A)
--       {J : Type*} (f : J → MvPolynomial ι K) :
--       primeLength Q (Ideal.span (Set.range f)) =
--         primeLength (WeightedBezout.pointIdeal (slicePoint Q A))
--           (Ideal.span (Set.range (fun j =>
--             WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q) (f j))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.WeightedBezout.pointIdeal` and `OAI.PiExponent.WeightedBezout.pointIdeal_isMaximal` (definitions bundle `OAIQ068A002` of this split); `OAI.PiExponent.CoordinateFiniteSlice.residueCoordinates`, `OAI.PiExponent.CoordinateFiniteSlice.slicePoint`, `OAI.PiExponent.CoordinateSliceComparison.primeLength` and `OAI.PiExponent.WeightedSliceDegree.enumeratedSliceMap` (definitions bundle `OAIQ068A006` of this split); `OAI.PiExponent.polynomialTangent` and `OAI.PiExponent.NormalBasisRigidity.IsNormalBasis` (definitions bundle `OAIQ068A007` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.PrimeWeightedBezout.weighted_prime_length_bound_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Approximation/CoordinateSliceComparison.lean (declaration OAI.PiExponent.CoordinateSliceComparison.length_eq_sliceFamily_of_normalBasis)

import Mathlib
import Definitions.Def_OAIQ068A002
import Definitions.Def_OAIQ068A006
import Definitions.Def_OAIQ068A007

section

attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CoordinateSliceComparison

open PiExponentJets.PolynomialLocalResidueResolution
open CoordinateFiniteSlice

variable {K ι : Type*} [Field K] [Fintype ι]

theorem length_eq_sliceFamily_of_normalBasis_q68 [CharZero K]
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hA : NormalBasisRigidity.IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent
        (IsScalarTower.toAlgHom K (MvPolynomial ι K) Q.ResidueField) Q).mkQ
        (Pi.basisFun Q.ResidueField ι i)) A)
    {J : Type*} (f : J → MvPolynomial ι K) :
    primeLength Q (Ideal.span (Set.range f)) =
      primeLength (WeightedBezout.pointIdeal (slicePoint Q A))
        (Ideal.span (Set.range (fun j =>
          WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q) (f j)))) := by
  sorry

end PiExponent.CoordinateSliceComparison

end

end OAI
end
