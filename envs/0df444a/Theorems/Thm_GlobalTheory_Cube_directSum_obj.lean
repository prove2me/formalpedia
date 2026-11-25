-- Prove2me | Theorems.Thm_GlobalTheory_Cube_directSum_obj
-- name    : GlobalTheory.Cube.directSum_obj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:45.842805+00:00
-- url     : https://prove2.me/theorems/ac683961-caaa-5e8a-bf88-745136d0574f
-- title:
--   Cube: direct Sum obj
-- statement:
--   The Cube construction uses the direct Sum obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L989-L990
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L989-L990

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
omit [DecidableEq κ]

theorem GlobalTheory.Cube.directSum_obj (A : κ → Cube.{v} ι R) (s : Finset ι) :
    (Cube.directSum A).obj s = ModuleCat.of R (⨁ k, (A k).obj s) := by sorry
