-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_filt_le_canonSpan
-- name    : GroundTheory.Automorphic.HarishChandra.filt_le_canonSpan
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:30:14.338649+00:00
-- url     : https://prove2.me/theorems/ec5d196e-a409-4a03-9279-a9c126c71135
-- title:
--   Harish Chandra: filt le canon Span
-- statement:
--   The Harish Chandra construction uses the filt le canon Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L310-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L310-L313

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

theorem GroundTheory.Automorphic.HarishChandra.filt_le_canonSpan (d : ℕ) : filt (n := n) d ≤ canonSpan (fun _ => True) 0 d := by sorry
