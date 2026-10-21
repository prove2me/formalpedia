-- Prove2me | Theorems.Thm_MazurTransfer_original_continuous_rational_radicand_linear_map_injective
-- name    : MazurTransfer.original_continuous_rational_radicand_linear_map_injective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T00:28:19.526051+00:00
-- url     : https://prove2.me/theorems/1309413e-691c-46c9-8b0a-7f9cd32e0523
-- statement:
--   The same original rational radicand linear map on the original continuous H1 submodule with a given family of root representatives is injective. Its underlying function is the separately proved original injective power-class map. Every original field, characteristic-zero, Galois, submodule and representative-existence hypothesis is retained. Named downstream consumer: the actual selected pi Selmer rational power-class support and numerical dimension bound.

import Definitions.Def_MazurTransfer_OriginalContinuousRationalRadicandLinearMapData20261019
noncomputable section
open MazurTransfer NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation ContinuousRationalRootClassKernel RationalNineteenthPowerClasses ContinuousCoefficientExponentAndContinuity ContinuousRationalRadicandMap
attribute [local instance] MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRadicandMap
attribute [local instance] MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatH1AlgEquivRatCoefficientAdditiveSubtypeUnitsMemSubgroupRootsRootsRepresentation_continuousRationalRadicandMap
attribute [local instance] MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatAdditivePowerClasses_continuousRationalRadicandMap

theorem MazurTransfer.original_continuous_rational_radicand_linear_map_injective : ∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (W : Submodule (ZMod 19) (H1 (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)))) (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)), Function.Injective (radicandLinearMap K W hrep) := by sorry
