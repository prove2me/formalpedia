-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_eq_prod
-- name    : GroundTheory.Automorphic.HarishChandra.canon_eq_prod
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:59.169325+00:00
-- url     : https://prove2.me/theorems/e1a08276-685f-4828-8344-0263fe3873da
-- title:
--   Harish Chandra: canon eq prod
-- statement:
--   The Harish Chandra construction uses the canon eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L155-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L155-L157

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

theorem GroundTheory.Automorphic.HarishChandra.canon_eq_prod (m : Fin n × Fin n →₀ ℕ) :
    canon m = ((letters n).map fun a => e a ^ m a).prod := by sorry
