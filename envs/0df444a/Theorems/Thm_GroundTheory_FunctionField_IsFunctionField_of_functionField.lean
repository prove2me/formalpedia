-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_IsFunctionField_of_functionField
-- name    : GroundTheory.FunctionField.IsFunctionField.of_functionField
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:52.885289+00:00
-- url     : https://prove2.me/theorems/ef67b075-821f-4902-a736-57815dac73ec
-- title:
--   Is Function Field: of function Field
-- statement:
--   The Is Function Field construction uses the of function Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBridge.lean#L188-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBridge.lean#L188-L197

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IsDedekindDomain IsLocalRing
open scoped WithZero
open GroundTheory.FunctionField.Place
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
open scoped Polynomial
omit [Algebra k K]

theorem GroundTheory.FunctionField.IsFunctionField.of_functionField [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K] :
    IsFunctionField k K := by sorry
