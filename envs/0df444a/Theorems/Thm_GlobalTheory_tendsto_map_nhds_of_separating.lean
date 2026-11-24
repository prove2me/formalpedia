-- Prove2me | Theorems.Thm_GlobalTheory_tendsto_map_nhds_of_separating
-- name    : GlobalTheory.tendsto_map_nhds_of_separating
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:36.538667+00:00
-- url     : https://prove2.me/theorems/5e6ce089-0a5b-4e43-8b56-bc0a4d2df774
-- title:
--   Global Theory: tendsto map nhds of separating
-- statement:
--   The Global Theory construction uses the tendsto map nhds of separating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsUniqueLinearLiftOfHolomorphicAbelianVariet.lean#L15-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsUniqueLinearLiftOfHolomorphicAbelianVariet.lean#L15-L70

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

theorem GlobalTheory.tendsto_map_nhds_of_separating [CompleteSpace V] [ProperSpace W] {ex : W →+ A}
    (hex : Function.Surjective ex) {G : V →+ A} {S : Set A} (h0 : (0 : A) ∈ S) {f : ι → A → Y}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, (∀ i, f i a = f i b) → a = b)
    (hSe : IsOpen (ex ⁻¹' S)) (hSG : IsOpen (G ⁻¹' S))
    (hfe : ∀ i, ContinuousOn (fun w ↦ f i (ex w)) (ex ⁻¹' S))
    (hfG : ∀ i, ContinuousOn (fun z ↦ f i (G z)) (G ⁻¹' S)) :
    ∀ N ∈ 𝓝 (0 : W), ∀ᶠ z in 𝓝 (0 : V), G z ∈ ex '' N := by sorry
