-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplex_directSum_exactAt_iff
-- name    : GlobalTheory.cubeComplex_directSum_exactAt_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:01.567598+00:00
-- url     : https://prove2.me/theorems/f4c0359d-ac50-43f9-90bf-fe5fd9b9ca75
-- title:
--   Global Theory: cube Complex direct Sum exact At iff
-- statement:
--   The Global Theory construction uses the cube Complex direct Sum exact At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L1139-L1145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L1139-L1145

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
variable [LinearOrder ι]
variable [Finite ι]
omit [DecidableEq κ]

theorem GlobalTheory.cubeComplex_directSum_exactAt_iff (A : κ → Cube.{v} ι R) (p : ℕ) :
    (cubeComplex (Cube.directSum A)).ExactAt p ↔ ∀ k, (cubeComplex (A k)).ExactAt p := by sorry
