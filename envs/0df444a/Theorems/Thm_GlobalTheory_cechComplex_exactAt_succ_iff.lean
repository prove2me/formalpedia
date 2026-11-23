-- Prove2me | Theorems.Thm_GlobalTheory_cechComplex_exactAt_succ_iff
-- name    : GlobalTheory.cechComplex_exactAt_succ_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:44:39.053419+00:00
-- url     : https://prove2.me/theorems/defe357f-1445-4e1c-a62b-f4909e346b2f
-- title:
--   Global Theory: cech Complex exact At succ iff
-- statement:
--   The Global Theory construction uses the cech Complex exact At succ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L494-L500
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L494-L500

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
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]

theorem GlobalTheory.cechComplex_exactAt_succ_iff (A : Cube.{v} ι R) (p : ℕ) :
    (cechComplex A).ExactAt (p + 1) ↔ Function.Exact (Cube.d A (p + 1)) (Cube.d A (p + 2)) := by sorry
