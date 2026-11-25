-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_diag_mul_sub
-- name    : GroundTheory.Automorphic.HarishChandra.e_diag_mul_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:37.770928+00:00
-- url     : https://prove2.me/theorems/94dd19be-db84-47ed-b824-9fc436797de7
-- title:
--   Harish Chandra: e diag mul sub
-- statement:
--   The Harish Chandra construction uses the e diag mul sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L324-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L324-L333

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

theorem GroundTheory.Automorphic.HarishChandra.e_diag_mul_sub (k : Fin n) (a : Fin n × Fin n) :
    e (k, k) * e a - e a * e (k, k) = (rootAt a k : ℂ) • e a := by sorry
