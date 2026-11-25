-- Prove2me | Theorems.Thm_GlobalTheory_Cube_d_restrictScalars_apply
-- name    : GlobalTheory.Cube.d_restrictScalars_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:46.008152+00:00
-- url     : https://prove2.me/theorems/bc5a898d-cd98-5baa-a2ea-5a583f2f5492
-- title:
--   Cube: d restrict Scalars apply
-- statement:
--   The Cube construction uses the d restrict Scalars apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L812-L815
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L812-L815

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
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] (f : R →+* S)

theorem GlobalTheory.Cube.d_restrictScalars_apply (A : Cube.{v} ι S) (p : ℕ) (x : Cube.Term A p) :
    Cube.d (A ⋙ ModuleCat.restrictScalars f) p x = Cube.d A p x := by sorry
