-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_valuation_lt_one_iff
-- name    : GroundTheory.FunctionField.Place.valuation_lt_one_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:04.295111+00:00
-- url     : https://prove2.me/theorems/08054ab9-4c37-45a1-87e9-1f908e977c46
-- title:
--   Place: valuation lt one iff
-- statement:
--   The Place construction uses the valuation lt one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L401-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L401-L402

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

theorem GroundTheory.FunctionField.Place.valuation_lt_one_iff (x : K) : v.valuation x < 1 ↔ v.ring.valuation x < 1 := by sorry
