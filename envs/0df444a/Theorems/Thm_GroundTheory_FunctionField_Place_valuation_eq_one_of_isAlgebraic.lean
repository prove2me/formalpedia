-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_valuation_eq_one_of_isAlgebraic
-- name    : GroundTheory.FunctionField.Place.valuation_eq_one_of_isAlgebraic
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:32.507564+00:00
-- url     : https://prove2.me/theorems/63e04515-844b-4503-819d-0c471e1a9aad
-- title:
--   Place: valuation eq one of is Algebraic
-- statement:
--   The Place construction uses the valuation eq one of is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBasic.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBasic.lean#L21-L27

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

theorem GroundTheory.FunctionField.Place.valuation_eq_one_of_isAlgebraic (v : Place k K) {x : K} (hx : IsAlgebraic k x)
    (hx0 : x ≠ 0) : v.ring.valuation x = 1 := by sorry
