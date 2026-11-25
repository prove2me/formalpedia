-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_sum_rootAt_expand
-- name    : GroundTheory.Automorphic.HarishChandra.sum_rootAt_expand
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:56.618958+00:00
-- url     : https://prove2.me/theorems/53f78cd3-5b6e-4363-aeaf-1fc65aec21cf
-- title:
--   Harish Chandra: sum root At expand
-- statement:
--   The Harish Chandra construction uses the sum root At expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L349-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L349-L363

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

theorem GroundTheory.Automorphic.HarishChandra.sum_rootAt_expand (m : Fin n × Fin n →₀ ℕ) (k : Fin n) :
    ((expand m).map fun a => rootAt a k).sum = wt m k := by sorry
