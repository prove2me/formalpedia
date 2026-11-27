-- Prove2me | Theorems.Thm_GlobalTheory_cechComplex_directSum_exactAt_iff
-- name    : GlobalTheory.cechComplex_directSum_exactAt_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:43:15.470415+00:00
-- url     : https://prove2.me/theorems/4d34058d-fce7-5f7f-91c7-d3fe35f5f1d6
-- title:
--   Global Theory: cech Complex direct Sum exact At iff
-- statement:
--   The Global Theory construction uses the cech Complex direct Sum exact At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L1149-L1155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L1149-L1155

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

theorem GlobalTheory.cechComplex_directSum_exactAt_iff (A : κ → Cube.{v} ι R) (p : ℕ) :
    (cechComplex (Cube.directSum A)).ExactAt p ↔ ∀ k, (cechComplex (A k)).ExactAt p := by sorry
