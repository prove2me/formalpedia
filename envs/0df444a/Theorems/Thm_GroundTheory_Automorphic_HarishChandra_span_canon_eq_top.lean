-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_span_canon_eq_top
-- name    : GroundTheory.Automorphic.HarishChandra.span_canon_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:59.906836+00:00
-- url     : https://prove2.me/theorems/ceaf9b2e-1211-4d02-b8a8-4487994b57ca
-- title:
--   Harish Chandra: span canon eq top
-- statement:
--   The Harish Chandra construction uses the span canon eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L262-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L262-L293

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

theorem GroundTheory.Automorphic.HarishChandra.span_canon_eq_top : Submodule.span ℂ (Set.range (canon (n := n))) = ⊤ := by sorry
