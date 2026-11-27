-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_liesOver_comap
-- name    : GroundTheory.FunctionField.Place.liesOver_comap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:20.82165+00:00
-- url     : https://prove2.me/theorems/00d4b224-1dca-54da-a89c-73bccf7f6cad
-- title:
--   Place: lies Over comap
-- statement:
--   The Place construction uses the lies Over comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L42-L43

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

theorem GroundTheory.FunctionField.Place.liesOver_comap [Algebra.IsAlgebraic K K'] (w : Place k K') : w.LiesOver (w.comap (K := K)) := by sorry
