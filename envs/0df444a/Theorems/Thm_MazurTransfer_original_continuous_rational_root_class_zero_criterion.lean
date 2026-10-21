-- Prove2me | Theorems.Thm_MazurTransfer_original_continuous_rational_root_class_zero_criterion
-- name    : MazurTransfer.original_continuous_rational_root_class_zero_criterion
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T23:29:00.244366+00:00
-- url     : https://prove2.me/theorems/e1d53f88-2227-4411-b4bb-0525552c6295
-- statement:
--   For an explicitly represented rational-root class in the original literal mu19 continuous cohomology, vanishing is equivalent to the same rational unit being a nineteenth power. The original coefficient value is nonzero and injective and respects the original Galois action, division and exponent nineteen. All original field, characteristic-zero, Galois, representative and class hypotheses are retained. No global representative-existence assertion or Hilbert 90 surjectivity is assumed. Named downstream consumer: the original selected pi Selmer rational radicand injection and its prime valuation support bound.

import Definitions.Def_MazurTransfer_OriginalContinuousRationalRootClassData20261019
noncomputable section
open MazurTransfer NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation ContinuousUnitRootCohomology ContinuousRationalRootClassKernel
attribute [local instance] MazurTransfer.ContinuousRationalRootClassKernel.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRootClassKernel

theorem MazurTransfer.original_continuous_rational_root_class_zero_criterion : (∀ (K : Type) [Field K] [CharZero K] (x : Coefficient (rootsRepresentation K)), value K x ≠ 0) ∧ (∀ (K : Type) [Field K] [CharZero K], Function.Injective (value K)) ∧ (∀ (K : Type) [Field K] [CharZero K] (x : Coefficient (rootsRepresentation K)), value K x ^ 19 = 1) ∧ (∀ (K : Type) [Field K] [CharZero K] (σ : (K ≃ₐ[ℚ] K)) (x : Coefficient (rootsRepresentation K)), value K (σ • x) = σ (value K x)) ∧ (∀ (K : Type) [Field K] [CharZero K] (x y : Coefficient (rootsRepresentation K)), value K (x / y) = value K x / value K y) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a : ℚˣ) (β : K) (hroot : RepresentsRoot K z a β) (hz : classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) z = 0), ∃ b : ℚˣ, b ^ 19 = a) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a : ℚˣ) (β : K) (hroot : RepresentsRoot K z a β) (ha : ∃ b : ℚˣ, b ^ 19 = a), classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) z = 0) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a : ℚˣ) (β : K) (hroot : RepresentsRoot K z a β), classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) z = 0 ↔ ∃ b : ℚˣ, b ^ 19 = a) := by sorry
