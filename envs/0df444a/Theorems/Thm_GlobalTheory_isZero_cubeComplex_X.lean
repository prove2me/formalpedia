-- Prove2me | Theorems.Thm_GlobalTheory_isZero_cubeComplex_X
-- name    : GlobalTheory.isZero_cubeComplex_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:09.698218+00:00
-- url     : https://prove2.me/theorems/266d7a27-e63f-4ebb-8cad-271533b67397
-- title:
--   Global Theory: is Zero cube Complex X
-- statement:
--   The Global Theory construction uses the is Zero cube Complex X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L547-L550
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L547-L550

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

theorem GlobalTheory.isZero_cubeComplex_X [Fintype ι] (A : Cube.{v} ι R) {p : ℕ} (h : Fintype.card ι < p) :
    IsZero ((cubeComplex A).X p) := by sorry
