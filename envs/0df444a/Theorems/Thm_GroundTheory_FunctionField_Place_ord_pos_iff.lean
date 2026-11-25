-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_ord_pos_iff
-- name    : GroundTheory.FunctionField.Place.ord_pos_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:35.413275+00:00
-- url     : https://prove2.me/theorems/12aad37b-dedf-4453-bb8f-d3d64b6a301c
-- title:
--   Place: ord pos iff
-- statement:
--   The Place construction uses the ord pos iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L453-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L453-L456

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IntermediateField
open scoped WithZero
open Polynomial
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
open GroundTheory.FunctionField.Place
variable {k K} (v : Place k K)
variable [IsFunctionField k K]

theorem GroundTheory.FunctionField.Place.ord_pos_iff {x : K} (hx : x ≠ 0) : 0 < v.ord x ↔ v.ring.valuation x < 1 := by sorry
