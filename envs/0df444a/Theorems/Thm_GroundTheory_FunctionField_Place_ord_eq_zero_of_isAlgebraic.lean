-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_ord_eq_zero_of_isAlgebraic
-- name    : GroundTheory.FunctionField.Place.ord_eq_zero_of_isAlgebraic
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:41.505266+00:00
-- url     : https://prove2.me/theorems/8f4c22e4-d93e-4e7d-a43c-ecce972819fd
-- title:
--   Place: ord eq zero of is Algebraic
-- statement:
--   The Place construction uses the ord eq zero of is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBasic.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBasic.lean#L29-L33

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

theorem GroundTheory.FunctionField.Place.ord_eq_zero_of_isAlgebraic [IsFunctionField k K] (v : Place k K) {x : K}
    (hx : IsAlgebraic k x) (hx0 : x ≠ 0) : v.ord x = 0 := by sorry
