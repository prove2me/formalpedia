-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_deg_eq
-- name    : GroundTheory.FunctionField.Place.LiesOver.deg_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:29.017566+00:00
-- url     : https://prove2.me/theorems/f116cb42-fb32-4b56-9b3e-a62776de52c1
-- title:
--   Lies Over: deg eq
-- statement:
--   The Lies Over construction uses the deg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L232-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L232-L236

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

theorem GroundTheory.FunctionField.Place.LiesOver.deg_eq {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    w.deg = w.inertiaDeg v * v.deg := by sorry
