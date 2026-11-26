-- Prove2me | Theorems.Thm_GlobalTheory_cubeSign_eq_or
-- name    : GlobalTheory.cubeSign_eq_or
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:28.897105+00:00
-- url     : https://prove2.me/theorems/b2f29b3d-4419-414d-b1f0-fce1fcc534e8
-- title:
--   Global Theory: cube Sign eq or
-- statement:
--   The Global Theory construction uses the cube Sign eq or property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L21-L22

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
variable {ι : Type} [LinearOrder ι]

theorem GlobalTheory.cubeSign_eq_or (t : Finset ι) (i : ι) : cubeSign t i = 1 ∨ cubeSign t i = -1 := by sorry
