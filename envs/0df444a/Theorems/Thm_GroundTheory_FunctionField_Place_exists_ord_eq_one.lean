-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_exists_ord_eq_one
-- name    : GroundTheory.FunctionField.Place.exists_ord_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:22.308724+00:00
-- url     : https://prove2.me/theorems/c17021f0-9b8b-47e3-a45c-607c847f7bbe
-- title:
--   Place: exists ord eq one
-- statement:
--   The Place construction uses the exists ord eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L468-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L468-L472

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

theorem GroundTheory.FunctionField.Place.exists_ord_eq_one : ∃ π : K, v.ord π = 1 := by sorry
