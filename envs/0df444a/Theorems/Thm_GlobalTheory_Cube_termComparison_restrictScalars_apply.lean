-- Prove2me | Theorems.Thm_GlobalTheory_Cube_termComparison_restrictScalars_apply
-- name    : GlobalTheory.Cube.termComparison_restrictScalars_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:23.538134+00:00
-- url     : https://prove2.me/theorems/d145d120-7728-4fb7-bc4a-708cb8d22b2b
-- title:
--   Cube: term Comparison restrict Scalars apply
-- statement:
--   The Cube construction uses the term Comparison restrict Scalars apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L787-L789
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L787-L789

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
omit [LinearOrder ι]

theorem GlobalTheory.Cube.termComparison_restrictScalars_apply (A : Cube.{v} ι S) (p : ℕ) (x : Cube.Term A p)
    (s : {s : Finset ι // s.card = p}) :
    (Cube.termComparison (ModuleCat.restrictScalars f) A p).hom x s = x s := by sorry
