-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_isScalarTower
-- name    : GroundTheory.FunctionField.Place.LiesOver.isScalarTower
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:37:04.550575+00:00
-- url     : https://prove2.me/theorems/ff5a342b-8c4d-4f8d-bd39-67075eea98a6
-- title:
--   Lies Over: is Scalar Tower
-- statement:
--   The Lies Over construction uses the is Scalar Tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L116-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L116-L121

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open GroundTheory.FunctionField.Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']

theorem GroundTheory.FunctionField.Place.LiesOver.isScalarTower {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    let := h.algebra
    IsScalarTower k v.ring w.ring := by sorry
