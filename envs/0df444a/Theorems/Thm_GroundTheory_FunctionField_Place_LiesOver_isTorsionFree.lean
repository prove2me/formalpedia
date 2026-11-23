-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_isTorsionFree
-- name    : GroundTheory.FunctionField.Place.LiesOver.isTorsionFree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:43.734854+00:00
-- url     : https://prove2.me/theorems/61ad1914-3401-45f8-801b-79ba0071b561
-- title:
--   Lies Over: is Torsion Free
-- statement:
--   The Lies Over construction uses the is Torsion Free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L163-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L163-L168

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
variable [IsFunctionField k K']
omit [IsFunctionField k K] [IsFunctionField k K'] [IsScalarTower k K K']

theorem GroundTheory.FunctionField.Place.LiesOver.isTorsionFree {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    Module.IsTorsionFree v.ring w.ring := by sorry
