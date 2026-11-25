-- Prove2me | Theorems.Thm_GlobalTheory_Cube_res_directSum
-- name    : GlobalTheory.Cube.res_directSum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:48.155683+00:00
-- url     : https://prove2.me/theorems/7eb58f5d-96b0-55c4-8d0d-4d9b642f0ac4
-- title:
--   Cube: res direct Sum
-- statement:
--   The Cube construction uses the res direct Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L994-L995
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L994-L995

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
open DirectSum
variable {R : Type u} [Ring R] {κ : Type} [DecidableEq κ]
variable {ι : Type}
omit [DecidableEq κ]

theorem GlobalTheory.Cube.res_directSum (A : κ → Cube.{v} ι R) {s t : Finset ι} (h : s ⊆ t) :
    Cube.res (Cube.directSum A) h = DirectSum.lmap fun k => Cube.res (A k) h := by sorry
