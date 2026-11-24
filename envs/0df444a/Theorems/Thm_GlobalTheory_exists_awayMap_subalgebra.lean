-- Prove2me | Theorems.Thm_GlobalTheory_exists_awayMap_subalgebra
-- name    : GlobalTheory.exists_awayMap_subalgebra
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:09.885645+00:00
-- url     : https://prove2.me/theorems/62eec414-e2cf-4aad-a073-352b9d423ff0
-- title:
--   Global Theory: exists away Map subalgebra
-- statement:
--   The Global Theory construction uses the exists away Map subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFgSubalgebraDescAway.lean#L6-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFgSubalgebraDescAway.lean#L6-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAwaySubalgebraEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFgSubalgebraDescAway
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_awayMap_subalgebra (K : Type) [Field K] (S : Type) [CommRing S] [Algebra K S]
    (S₁ : Subalgebra K S) (x : S) (hx : x ∈ S₁) :
    ∃ κ : Localization.Away (⟨x, hx⟩ : S₁) →ₐ[K] Localization.Away x,
      (∀ s : S₁, κ (algebraMap S₁ _ s) = algebraMap S _ (s : S)) ∧ Function.Injective κ ∧
      ∀ (z : Localization.Away x) (m : ℕ) (s : S), s ∈ S₁ →
        z * algebraMap S _ x ^ m = algebraMap S _ s → z ∈ κ.range := by sorry
