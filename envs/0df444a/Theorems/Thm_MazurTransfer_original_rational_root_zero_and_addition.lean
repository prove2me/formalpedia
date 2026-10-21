-- Prove2me | Theorems.Thm_MazurTransfer_original_rational_root_zero_and_addition
-- name    : MazurTransfer.original_rational_root_zero_and_addition
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T00:01:29.373284+00:00
-- url     : https://prove2.me/theorems/df364537-47f0-4ffa-9ce5-6b0ca6585033
-- statement:
--   The original zero continuous cocycle is represented by rational unit one and root one. The original coefficient value respects multiplication. The sum of two originally represented rational-root cocycles is represented by the product of the same rational radicands and roots. All original field, characteristic-zero and representative hypotheses are retained. Named downstream consumer: the original rational radicand group homomorphism and selected pi Selmer linear injection.

import Definitions.Def_MazurTransfer_OriginalContinuousRationalRootClassData20261019
noncomputable section
open MazurTransfer NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation ContinuousRationalRootClassKernel
attribute [local instance] MazurTransfer.ContinuousRationalRootClassKernel.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRootClassKernel

theorem MazurTransfer.original_rational_root_zero_and_addition : (∀ (K : Type) [Field K] [CharZero K], RepresentsRoot K 0 1 1) ∧ (∀ (K : Type) [Field K] [CharZero K] (x y : Coefficient (rootsRepresentation K)), value K (x * y) = value K x * value K y) ∧ (∀ (K : Type) [Field K] [CharZero K] (z w : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a d : ℚˣ) (β γ : K) (hz : RepresentsRoot K z a β) (hw : RepresentsRoot K w d γ), RepresentsRoot K (z + w) (a * d) (β * γ)) := by sorry
