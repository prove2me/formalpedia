-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_min_le_ord_add
-- name    : GroundTheory.FunctionField.Place.min_le_ord_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:36.654397+00:00
-- url     : https://prove2.me/theorems/4af977ef-9ceb-45d3-a8c1-7442c1793164
-- title:
--   Place: min le ord add
-- statement:
--   The Place construction uses the min le ord add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L461-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L461-L466

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

theorem GroundTheory.FunctionField.Place.min_le_ord_add {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (v.ord x) (v.ord y) ≤ v.ord (x + y) := by sorry
