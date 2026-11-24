-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_wordSpan_le_filt
-- name    : GroundTheory.Automorphic.HarishChandra.wordSpan_le_filt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:47.823483+00:00
-- url     : https://prove2.me/theorems/7f380e56-502e-4018-826e-a32dceb6724e
-- title:
--   Harish Chandra: word Span le filt
-- statement:
--   The Harish Chandra construction uses the word Span le filt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L307-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L307-L308

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.wordSpan_le_filt (P : Fin n × Fin n → Prop) (k : ℕ) : wordSpan (n := n) P k ≤ filt k := by sorry
