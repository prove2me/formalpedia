-- Prove2me | Theorems.Thm_GlobalTheory_isDVR_of_closed_subring_principal
-- name    : GlobalTheory.isDVR_of_closed_subring_principal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:54.363324+00:00
-- url     : https://prove2.me/theorems/4066e8aa-aa12-4af4-bed9-7dce28308b62
-- title:
--   Global Theory: is DVR of closed subring principal
-- statement:
--   The Global Theory construction uses the is DVR of closed subring principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsDVROfClosedSubringPrincipal.lean#L87-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsDVROfClosedSubringPrincipal.lean#L87-L177

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDVROfClosedSubringPrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.isDVR_of_closed_subring_principal :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] (Λ : Subring S) (π : Λ), (π : S) ≠ 0 → (π : S) ∈ maximalIdeal S → IsAdicComplete (maximalIdeal S) S → (∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S) → (∀ a : Λ, (a : S) ∈ maximalIdeal S → π ∣ a) → (∀ s : S, (∀ n : ℕ, ∃ a ∈ Λ, s - a ∈ maximalIdeal S ^ n) → s ∈ Λ) → ∃ _ : IsDiscreteValuationRing Λ, maximalIdeal Λ = Ideal.span {π} ∧ IsAdicComplete (maximalIdeal Λ) Λ := by sorry
