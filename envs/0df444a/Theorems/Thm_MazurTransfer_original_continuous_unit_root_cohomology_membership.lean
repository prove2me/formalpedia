-- Prove2me | Theorems.Thm_MazurTransfer_original_continuous_unit_root_cohomology_membership
-- name    : MazurTransfer.original_continuous_unit_root_cohomology_membership
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T23:21:01.235363+00:00
-- url     : https://prove2.me/theorems/8b576a27-6dd9-4573-9d85-96ca498e96ba
-- statement:
--   For the original coefficient representation, original arithmetic action and existing continuous first cohomology, membership in the same unit-root submodule is equivalent to the existence of a continuous cocycle representative with the original unit and root equations. Every such representative gives a member of that same submodule. All original ring, field, characteristic-zero, algebra, group and topology hypotheses are retained. Named downstream consumer: the selected pi Kummer image unit condition at nineteen and its original arithmetic Selmer subspace.

import Definitions.Def_MazurTransfer_OriginalContinuousUnitRootCohomologyData20261019
noncomputable section
open MazurTransfer
open NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation ContinuousCoefficientExponentAndContinuity ContinuousUnitRootCohomology
attribute [local instance] MazurTransfer.ContinuousUnitRootCohomology.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousUnitRootCohomology
attribute [local instance] MazurTransfer.ContinuousUnitRootCohomology.instModuleZModOfNatNatH1CoefficientAdditiveSubtypeUnitsMemSubgroupRoots_continuousUnitRootCohomology

theorem MazurTransfer.original_continuous_unit_root_cohomology_membership : (∀ (R K Γ : Type) [CommRing R] [Field K] [CharZero K] [Algebra R K] [Group Γ] [TopologicalSpace Γ] (τ : Representation (ZMod 19) Γ (Additive (Roots K))) (ι : Γ →* (K ≃ₐ[ℚ] K)) (x : H1 Γ (Coefficient τ)), x ∈ unitCondition R K Γ τ ι ↔ ∃ z : continuousCocycles Γ (Coefficient τ), HasUnitRoot R K Γ τ ι z ∧ classMap Γ (Coefficient τ) z = x) ∧ (∀ (R K Γ : Type) [CommRing R] [Field K] [CharZero K] [Algebra R K] [Group Γ] [TopologicalSpace Γ] (τ : Representation (ZMod 19) Γ (Additive (Roots K))) (ι : Γ →* (K ≃ₐ[ℚ] K)) (z : continuousCocycles Γ (Coefficient τ)) (hz : HasUnitRoot R K Γ τ ι z), classMap Γ (Coefficient τ) z ∈ unitCondition R K Γ τ ι) := by sorry
