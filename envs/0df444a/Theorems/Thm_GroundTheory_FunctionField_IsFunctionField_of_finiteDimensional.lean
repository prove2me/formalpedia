-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_IsFunctionField_of_finiteDimensional
-- name    : GroundTheory.FunctionField.IsFunctionField.of_finiteDimensional
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:37:14.385586+00:00
-- url     : https://prove2.me/theorems/823f523d-7562-4953-a177-372e214fa0b0
-- title:
--   Is Function Field: of finite Dimensional
-- statement:
--   The Is Function Field construction uses the of finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L123-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L123-L137

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

theorem GroundTheory.FunctionField.IsFunctionField.of_finiteDimensional [IsFunctionField k K]
    [FiniteDimensional K K'] : IsFunctionField k K' := by sorry
