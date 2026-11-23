-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_valuation_eq_exp_neg_ord
-- name    : GroundTheory.FunctionField.Place.valuation_eq_exp_neg_ord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:20.658007+00:00
-- url     : https://prove2.me/theorems/2591aed1-8eb2-4d06-a061-af5eac0177ed
-- title:
--   Place: valuation eq exp neg ord
-- statement:
--   The Place construction uses the valuation eq exp neg ord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L412-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L412-L414

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

theorem GroundTheory.FunctionField.Place.valuation_eq_exp_neg_ord {x : K} (hx : x ≠ 0) :
    v.valuation x = WithZero.exp (-v.ord x) := by sorry
