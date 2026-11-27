-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_ord_div
-- name    : GroundTheory.FunctionField.Place.ord_div
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:25.93689+00:00
-- url     : https://prove2.me/theorems/321d8048-ed99-4fe6-b9b2-fe874629426c
-- title:
--   Place: ord div
-- statement:
--   The Place construction uses the ord div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L435-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L435-L437

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

theorem GroundTheory.FunctionField.Place.ord_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : v.ord (x / y) = v.ord x - v.ord y := by sorry
