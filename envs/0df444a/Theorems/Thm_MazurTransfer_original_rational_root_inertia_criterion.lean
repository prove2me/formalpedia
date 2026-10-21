-- Prove2me | Theorems.Thm_MazurTransfer_original_rational_root_inertia_criterion
-- name    : MazurTransfer.original_rational_root_inertia_criterion
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T23:42:50.691137+00:00
-- url     : https://prove2.me/theorems/54db4dfb-de10-4bd5-8b7e-459c4198abd0
-- statement:
--   The original represented rational-root class restricts to zero exactly when its same radicand has a nonzero root fixed by the same given subgroup. Every original field, characteristic-zero, subgroup, representation and class hypothesis is retained. Named downstream consumer: genuine valuation inertia divisibility for the original actual pi Selmer radicands.

import Definitions.Def_MazurTransfer_OriginalContinuousRationalRootClassData20261019
import Theorems.Thm_MazurTransfer_original_continuous_rational_root_class_zero_criterion
import Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionWithCoboundaryLawDataV220261018
noncomputable section
open MazurTransfer NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation ContinuousRationalRootClassKernel
open ContinuousFirstCohomologySubgroupRestriction
attribute [local instance] MazurTransfer.ContinuousRationalRootClassKernel.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRootClassKernel

theorem MazurTransfer.original_rational_root_inertia_criterion : (∀ (K : Type) [Field K] [CharZero K] (S : Subgroup (K ≃ₐ[ℚ] K)) (z : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a : ℚˣ) (β : K) (hroot : RepresentsRoot K z a β) (hz : restriction (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) S (classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) z) = 0), ∃ α : K, α ≠ 0 ∧ α ^ 19 = algebraMap ℚ K (a : ℚ) ∧ ∀ σ : S, σ.val α = α) ∧ (∀ (K : Type) [Field K] [CharZero K] (S : Subgroup (K ≃ₐ[ℚ] K)) (z : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a : ℚˣ) (β : K) (hroot : RepresentsRoot K z a β) (ha : ∃ α : K, α ≠ 0 ∧ α ^ 19 = algebraMap ℚ K (a : ℚ) ∧ ∀ σ : S, σ.val α = α), restriction (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) S (classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) z) = 0) ∧ (∀ (K : Type) [Field K] [CharZero K] (S : Subgroup (K ≃ₐ[ℚ] K)) (z : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a : ℚˣ) (β : K) (hroot : RepresentsRoot K z a β), restriction (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) S (classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) z) = 0 ↔ ∃ α : K, α ≠ 0 ∧ α ^ 19 = algebraMap ℚ K (a : ℚ) ∧ ∀ σ : S, σ.val α = α) := by sorry
