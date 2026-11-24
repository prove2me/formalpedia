-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_linear_lift_of_separating
-- name    : GlobalTheory.existsUnique_linear_lift_of_separating
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:29.993276+00:00
-- url     : https://prove2.me/theorems/366c942a-b0e3-4496-8460-88db10f428c1
-- title:
--   Global Theory: exists Unique linear lift of separating
-- statement:
--   The Global Theory construction uses the exists Unique linear lift of separating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsUniqueLinearLiftOfHolomorphicAbelianVariet.lean#L72-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsUniqueLinearLiftOfHolomorphicAbelianVariet.lean#L72-L124

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set Metric
open GlobalTheory
variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W] {A : Type*} [AddCommGroup A]
  {ι : Type*} {Y : Type*} [TopologicalSpace Y] [T2Space Y]

theorem GlobalTheory.existsUnique_linear_lift_of_separating [NormedSpace ℂ V] [NormedSpace ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {ex : W →+ A}
    (hex : Function.Surjective ex) (hker : IsDiscrete (ex.ker : Set W))
    {G : V →+ A} {S : Set A} (h0 : (0 : A) ∈ S) {f : ι → A → ℂ}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, (∀ i, f i a = f i b) → a = b)
    (hSe : IsOpen (ex ⁻¹' S)) (hSG : IsOpen (G ⁻¹' S))
    (hfe : ∀ i, DifferentiableOn ℂ (fun w ↦ f i (ex w)) (ex ⁻¹' S))
    (hfG : ∀ i, DifferentiableOn ℂ (fun z ↦ f i (G z)) (G ⁻¹' S))
    (hD : ∀ w, (∀ i, fderiv ℂ (fun w ↦ f i (ex w)) 0 w = 0) → w = 0) :
    ∃! F : V →ₗ[ℂ] W, ∀ z, ex (F z) = G z := by sorry
