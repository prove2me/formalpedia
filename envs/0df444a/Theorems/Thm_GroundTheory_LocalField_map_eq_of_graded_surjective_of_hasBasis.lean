-- Prove2me | Theorems.Thm_GroundTheory_LocalField_map_eq_of_graded_surjective_of_hasBasis
-- name    : GroundTheory.LocalField.map_eq_of_graded_surjective_of_hasBasis
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:59:58.974473+00:00
-- url     : https://prove2.me/theorems/adf458b7-0d4e-5fca-894f-ad87f84a6cd3
-- title:
--   Local Field: map eq of graded surjective of has Basis
-- statement:
--   The Local Field construction uses the map eq of graded surjective of has Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FilteredSurj.lean#L187-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FilteredSurj.lean#L187-L197

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Filter Topology Uniformity

theorem GroundTheory.LocalField.map_eq_of_graded_surjective_of_hasBasis {G H : Type*} [Group G] [UniformSpace G]
    [IsRightUniformGroup G] [CompleteSpace G] [Group H] [TopologicalSpace H] [T1Space H]
    {F : ℕ → Subgroup G} {E : ℕ → Subgroup H} (hF : Antitone F) (hE : Antitone E)
    (hFb : (𝓝 (1 : G)).HasBasis (fun _ => True) (fun n => (F n : Set G)))
    (hEb : (𝓝 (1 : H)).HasBasis (fun _ => True) (fun n => (E n : Set H)))
    (f : G →* H) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (k : ℕ) (hmap : ∀ n, k ≤ n → ∀ g ∈ F n, f g ∈ E (φ n))
    (hgr : ∀ n, k ≤ n → ∀ h ∈ E (φ n), ∃ g ∈ F n, h / f g ∈ E (φ (n + 1))) :
    (F k).map f = E (φ k) := by sorry
