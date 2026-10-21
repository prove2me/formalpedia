-- Prove2me | Theorems.Thm_MazurTransfer_original_rational_root_class_comparison
-- name    : MazurTransfer.original_rational_root_class_comparison
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T23:53:21.188385+00:00
-- url     : https://prove2.me/theorems/04efbe9a-40d4-4647-adcf-568a35f7217b
-- statement:
--   For the same two explicitly represented rational-root classes in the original literal mu19 continuous H1, equality is equivalent to the same rational radicand ratio being a nineteenth power. Their difference has the original quotient root as representative. All original field, characteristic-zero, Galois and representative hypotheses are retained. Named downstream consumer: the original rational radicand linear injection of the actual selected pi Selmer space.

import Definitions.Def_MazurTransfer_OriginalContinuousRationalRootClassData20261019
import Theorems.Thm_MazurTransfer_original_continuous_rational_root_class_zero_criterion
noncomputable section
open MazurTransfer NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation ContinuousRationalRootClassKernel
attribute [local instance] MazurTransfer.ContinuousRationalRootClassKernel.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRootClassKernel

theorem MazurTransfer.original_rational_root_class_comparison : (∀ (K : Type) [Field K] [CharZero K] (z w : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a d : ℚˣ) (β γ : K) (hz : RepresentsRoot K z a β) (hw : RepresentsRoot K w d γ), RepresentsRoot K (z - w) (a / d) (β / γ)) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z w : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a d : ℚˣ) (β γ : K) (hz : RepresentsRoot K z a β) (hw : RepresentsRoot K w d γ), classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) z = classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) w ↔ ∃ b : ℚˣ, b ^ 19 = a / d) := by sorry
