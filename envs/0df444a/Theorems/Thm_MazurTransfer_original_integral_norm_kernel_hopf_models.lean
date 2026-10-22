-- Prove2me | Theorems.Thm_MazurTransfer_original_integral_norm_kernel_hopf_models
-- name    : MazurTransfer.original_integral_norm_kernel_hopf_models
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T06:22:21.558828+00:00
-- url     : https://prove2.me/theorems/f4079de1-afd9-4763-a53a-42e358a3a0a6
-- statement:
--   Both same selected integral norm kernels have finite-free cocommutative Hopf models with the original local group multiplication and all algebra base-change maps at every prime away from 104, including nineteen. All original integral models, norms, prime and coefficient hypotheses are retained. Named downstream consumer: actual arithmetic kernel Hopf labels and finite-flat ordered character quotients at nineteen.

import Definitions.Def_MazurTransfer_OriginalExceptionalNineteenNormModelData20261020
import Definitions.Def_MazurTransfer_OriginalRelativeNormKernelSchemePointsAndGroupLawData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePi_isMonHom
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePiConjugate_isMonHom
import Theorems.Thm_MazurTransfer_original_relative_norm_kernel_hopf_representability
import Theorems.Thm_MazurTransfer_original_local_picard_group_law_commutative
import Theorems.Thm_MazurTransfer_original_integral_norms_finite_flat_all_good_primes
import Theorems.Thm_MazurTransfer_original_integral_norm_unit_and_all_point_identities
import Theorems.Thm_MazurTransfer_original_integral_norm_multiplication
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13GoodPrimeLocalPicardModels MazurTransfer.Order13GoodPrimeIntegralNormExtensions
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm MazurTransfer.Order13ActualPicardSchemeNormGroupHom
open MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf
open MazurTransfer.Order13ExceptionalNineteenFlatNormFibres
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup
attribute [local instance] MazurTransfer.Order13ActualPicardSchemeNormGroupHom.schemePi_isMonHom
attribute [local instance] MazurTransfer.Order13ActualPicardSchemeNormGroupHom.schemePiConjugate_isMonHom
attribute [local instance] MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.instFactPrimeOfNatNat_order13ExceptionalNineteenFlatNormFibres

theorem MazurTransfer.original_integral_norm_kernel_hopf_models : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104),
HasFiniteFreeKernelHopfModel (localLaw q hq) (integralPi q hq) ∧
      HasFiniteFreeKernelHopfModel (localLaw q hq) (integralPiConjugate q hq)) ∧ (HasFiniteFreeKernelHopfModel (localLaw 19 nineteen_good) (integralPi 19 nineteen_good) ∧
      HasFiniteFreeKernelHopfModel (localLaw 19 nineteen_good)
        (integralPiConjugate 19 nineteen_good)) := by sorry
