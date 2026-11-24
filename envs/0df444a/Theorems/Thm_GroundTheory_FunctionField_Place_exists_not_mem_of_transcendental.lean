-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_exists_not_mem_of_transcendental
-- name    : GroundTheory.FunctionField.Place.exists_not_mem_of_transcendental
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:42.747652+00:00
-- url     : https://prove2.me/theorems/1b00adde-2b9b-4a9c-b982-da3bd185110a
-- title:
--   Place: exists not mem of transcendental
-- statement:
--   The Place construction uses the exists not mem of transcendental property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBasic.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBasic.lean#L65-L73

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open Polynomial
open GroundTheory.FunctionField.Place
variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem GroundTheory.FunctionField.Place.exists_not_mem_of_transcendental {x : K} (hx : Transcendental k x) :
    ∃ v : Place k K, x ∉ v.ring := by sorry
