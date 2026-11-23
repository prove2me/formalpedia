-- Prove2me | Theorems.Thm_GlobalTheory_Cube_extend_apply_of_ne
-- name    : GlobalTheory.Cube.extend_apply_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:01.071037+00:00
-- url     : https://prove2.me/theorems/b0a1ed2b-09b1-44fa-8db4-6ef3e5e26b2a
-- title:
--   Cube: extend apply of ne
-- statement:
--   The Cube construction uses the extend apply of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L137-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L137-L138

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
open GlobalTheory.Cube
variable {ι : Type} {R : Type u} [Ring R]

theorem GlobalTheory.Cube.extend_apply_of_ne (A : Cube.{v} ι R) {p : ℕ} (x : Term A p) {s : Finset ι}
    (h : s.card ≠ p) : extend A p x s = 0 := by sorry
