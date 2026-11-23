-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_ord_uniformizer
-- name    : GroundTheory.FunctionField.Place.ord_uniformizer
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:05.391586+00:00
-- url     : https://prove2.me/theorems/7b0060d2-8e39-4a64-9ec1-6d4a0c3fc2a9
-- title:
--   Place: ord uniformizer
-- statement:
--   The Place construction uses the ord uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L146-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L146-L147

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
variable [IsFunctionField k K]

theorem GroundTheory.FunctionField.Place.ord_uniformizer (v : Place k K) : v.ord v.uniformizer = 1 := by sorry
