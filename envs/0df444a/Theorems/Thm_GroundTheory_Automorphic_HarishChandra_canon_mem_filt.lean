-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_mem_filt
-- name    : GroundTheory.Automorphic.HarishChandra.canon_mem_filt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:52:58.258715+00:00
-- url     : https://prove2.me/theorems/71e91143-b36e-545f-b72e-324f68c37493
-- title:
--   Harish Chandra: canon mem filt
-- statement:
--   The Harish Chandra construction uses the canon mem filt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L304-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L304-L305

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

theorem GroundTheory.Automorphic.HarishChandra.canon_mem_filt (m : Fin n × Fin n →₀ ℕ) : canon m ∈ filt (n := n) m.degree := by sorry
