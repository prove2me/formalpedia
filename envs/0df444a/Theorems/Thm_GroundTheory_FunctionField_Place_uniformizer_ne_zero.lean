-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_uniformizer_ne_zero
-- name    : GroundTheory.FunctionField.Place.uniformizer_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:26.140941+00:00
-- url     : https://prove2.me/theorems/2ed759a0-3e33-4344-b1dd-55c93c2be73b
-- title:
--   Place: uniformizer ne zero
-- statement:
--   The Place construction uses the uniformizer ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L149-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L149-L152

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

theorem GroundTheory.FunctionField.Place.uniformizer_ne_zero (v : Place k K) : v.uniformizer ≠ 0 := by sorry
