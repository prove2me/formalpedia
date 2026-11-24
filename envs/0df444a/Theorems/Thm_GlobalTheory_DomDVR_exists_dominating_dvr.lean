-- Prove2me | Theorems.Thm_GlobalTheory_DomDVR_exists_dominating_dvr
-- name    : GlobalTheory.DomDVR.exists_dominating_dvr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:50:06.215057+00:00
-- url     : https://prove2.me/theorems/97508722-24bd-41a2-b7a9-9f3ce2147c95
-- title:
--   Dom DVR: exists dominating dvr
-- statement:
--   The Dom DVR construction uses the exists dominating dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDominatingDvrContainingFinset.lean#L9-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDominatingDvrContainingFinset.lean#L9-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDominatingDvrContainingFinset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.DomDVR
set_option maxHeartbeats 1000000

theorem GlobalTheory.DomDVR.exists_dominating_dvr : ∀ (F : Type) [Field F] [CharZero F] (T' : Subring F), IsDiscreteValuationRing T' → ∀ (s : Finset F), (1 : F) ∈ Submodule.span T' (s : Set F) → (∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span T' (s : Set F)) → ∃ T'' : Subring F, IsDiscreteValuationRing T'' ∧ T' ≤ T'' ∧ (∀ x ∈ s, x ∈ T'') ∧ (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) ∧ (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) := by sorry
