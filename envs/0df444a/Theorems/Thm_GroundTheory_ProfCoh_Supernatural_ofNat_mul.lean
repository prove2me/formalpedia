-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_mul
-- name    : GroundTheory.ProfCoh.Supernatural.ofNat_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:20.474495+00:00
-- url     : https://prove2.me/theorems/7e4ecbc8-4c8f-418a-9eca-7c13217cfe09
-- title:
--   Supernatural: of Nat mul
-- statement:
--   The Supernatural construction uses the of Nat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L58-L60

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

theorem GroundTheory.ProfCoh.Supernatural.ofNat_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : ofNat (m * n) = ofNat m * ofNat n := by sorry
