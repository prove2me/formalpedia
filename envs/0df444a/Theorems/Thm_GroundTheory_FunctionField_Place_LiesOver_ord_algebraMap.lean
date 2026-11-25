-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_ord_algebraMap
-- name    : GroundTheory.FunctionField.Place.LiesOver.ord_algebraMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:37:10.798884+00:00
-- url     : https://prove2.me/theorems/831f38df-56aa-43b8-9dbd-2b7aa51dea2e
-- title:
--   Lies Over: ord algebra Map
-- statement:
--   The Lies Over construction uses the ord algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L200-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L200-L209

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Theorems.Thm_GroundTheory_FunctionField_Place_ord_algebraMap

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
variable [IsFunctionField k K]
variable [IsFunctionField k K']

theorem GroundTheory.FunctionField.Place.LiesOver.ord_algebraMap {w : Place k K'} {v : Place k K} (h : w.LiesOver v) (x : K) :
    w.ord (algebraMap K K' x) = w.ramificationIdx v * v.ord x := by sorry
