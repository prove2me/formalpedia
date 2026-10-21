-- Prove2me | Theorems.Thm_MazurTransfer_original_representative_independent_rational_power_class
-- name    : MazurTransfer.original_representative_independent_rational_power_class
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T00:10:54.359403+00:00
-- url     : https://prove2.me/theorems/1a5917f7-fce3-452b-b8b3-bf52d5879e36
-- statement:
--   For the same original submodule of literal mu19 continuous H1 with a given family of original rational-root representatives, every original representative gives the same rational nineteenth-power class. That original power-class function is injective and preserves zero and addition. The original record, choice, quotient, coefficients and every representative-existence hypothesis are retained. No global representative existence is asserted. Named downstream consumer: the original actual selected pi Selmer rational radicand linear injection.

import Definitions.Def_MazurTransfer_OriginalContinuousRationalRadicandRepresentativeData20261019
import Theorems.Thm_MazurTransfer_original_rational_nineteenth_power_class_equality_and_exponent
import Theorems.Thm_MazurTransfer_original_rational_root_class_comparison
import Theorems.Thm_MazurTransfer_original_rational_root_zero_and_addition
noncomputable section
open MazurTransfer NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation ContinuousRationalRootClassKernel RationalNineteenthPowerClasses ContinuousCoefficientExponentAndContinuity ContinuousRationalRadicandMap
attribute [local instance] MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRadicandMap
attribute [local instance] MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatH1AlgEquivRatCoefficientAdditiveSubtypeUnitsMemSubgroupRootsRootsRepresentation_continuousRationalRadicandMap
attribute [local instance] MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatAdditivePowerClasses_continuousRationalRadicandMap

theorem MazurTransfer.original_representative_independent_rational_power_class : (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (W : Submodule (ZMod 19) (H1 (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)))) (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)) (x : W) (c : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a : ℚˣ) (β : K) (hc : classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) c = x.val) (hroot : RepresentsRoot K c a β), classOf a = powerClass K W hrep x) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (W : Submodule (ZMod 19) (H1 (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)))) (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)), Function.Injective (powerClass K W hrep)) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (W : Submodule (ZMod 19) (H1 (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)))) (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)), powerClass K W hrep 0 = 1) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (W : Submodule (ZMod 19) (H1 (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)))) (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)) (x y : W), powerClass K W hrep (x + y) = powerClass K W hrep x * powerClass K W hrep y) := by sorry
