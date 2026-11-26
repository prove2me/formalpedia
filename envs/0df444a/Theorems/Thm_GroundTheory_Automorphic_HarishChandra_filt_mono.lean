-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_filt_mono
-- name    : GroundTheory.Automorphic.HarishChandra.filt_mono
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:53:28.294436+00:00
-- url     : https://prove2.me/theorems/83b74439-7361-496c-87df-b2faa2737ef2
-- title:
--   Harish Chandra: filt mono
-- statement:
--   The Harish Chandra construction uses the filt mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L301-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L301-L302

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

theorem GroundTheory.Automorphic.HarishChandra.filt_mono {d d' : ℕ} (h : d ≤ d') : filt (n := n) d ≤ filt d' := by sorry
