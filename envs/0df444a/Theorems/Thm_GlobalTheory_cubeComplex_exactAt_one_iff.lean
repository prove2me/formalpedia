-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplex_exactAt_one_iff
-- name    : GlobalTheory.cubeComplex_exactAt_one_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:39.940343+00:00
-- url     : https://prove2.me/theorems/ec5a9687-4427-4f96-8c37-238236fc5ecc
-- title:
--   Global Theory: cube Complex exact At one iff
-- statement:
--   The Global Theory construction uses the cube Complex exact At one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L485-L492
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L485-L492

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

theorem GlobalTheory.cubeComplex_exactAt_one_iff (A : Cube.{v} ι R) :
    (cubeComplex A).ExactAt 1 ↔ Function.Exact (Cube.aug A) (Cube.d A 1) := by sorry
