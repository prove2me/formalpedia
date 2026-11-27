-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_injective
-- name    : GroundTheory.ProfCoh.Supernatural.ofNat_injective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:02:13.001108+00:00
-- url     : https://prove2.me/theorems/1b0b65f9-0dc5-4c6f-a5d0-6a1cc174cfab
-- title:
--   Supernatural: of Nat injective
-- statement:
--   The Supernatural construction uses the of Nat injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L74-L77

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
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
open GroundTheory.ProfCoh.Supernatural

theorem GroundTheory.ProfCoh.Supernatural.ofNat_injective {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : ofNat m = ofNat n ↔ m = n := by sorry
