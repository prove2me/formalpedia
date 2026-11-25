-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_natCard_subtype_eq_sum_natCard_fiber
-- name    : GroundTheory.ProfCoh.natCard_subtype_eq_sum_natCard_fiber
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:57.796507+00:00
-- url     : https://prove2.me/theorems/994182e1-0693-4696-861e-5cd31ee71e0f
-- title:
--   Prof Coh: nat Card subtype eq sum nat Card fiber
-- statement:
--   The Prof Coh construction uses the nat Card subtype eq sum nat Card fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ArtinCount.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ArtinCount.lean#L8-L20

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_ArtinCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open MulAction

theorem GroundTheory.ProfCoh.natCard_subtype_eq_sum_natCard_fiber {α β : Type*} [Finite α] [DecidableEq β] (f : α → β)
    (t : Finset β) (P : α → Prop) (hP : ∀ a, P a ↔ f a ∈ t) :
    Nat.card {a // P a} = ∑ b ∈ t, Nat.card {a // f a = b} := by sorry
