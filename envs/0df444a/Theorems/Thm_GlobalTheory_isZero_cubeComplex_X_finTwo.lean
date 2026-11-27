-- Prove2me | Theorems.Thm_GlobalTheory_isZero_cubeComplex_X_finTwo
-- name    : GlobalTheory.isZero_cubeComplex_X_finTwo
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:27.989983+00:00
-- url     : https://prove2.me/theorems/82abff6e-6833-4c7b-a0d1-65b16b782e54
-- title:
--   Global Theory: is Zero cube Complex X fin Two
-- statement:
--   The Global Theory construction uses the is Zero cube Complex X fin Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L1199-L1201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L1199-L1201

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
variable {R : Type u} [Ring R]

theorem GlobalTheory.isZero_cubeComplex_X_finTwo (A : Cube.{v} (Fin 2) R) {p : ℕ} (h : 3 ≤ p) :
    IsZero ((cubeComplex A).X p) := by sorry
