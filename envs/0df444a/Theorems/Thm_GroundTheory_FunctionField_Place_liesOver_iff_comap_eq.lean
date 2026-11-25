-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_liesOver_iff_comap_eq
-- name    : GroundTheory.FunctionField.Place.liesOver_iff_comap_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:37:31.489911+00:00
-- url     : https://prove2.me/theorems/611e9725-3919-456e-bcdf-fe14b3eafe60
-- title:
--   Place: lies Over iff comap eq
-- statement:
--   The Place construction uses the lies Over iff comap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L45-L47

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

theorem GroundTheory.FunctionField.Place.liesOver_iff_comap_eq [Algebra.IsAlgebraic K K'] {w : Place k K'} {v : Place k K} :
    w.LiesOver v ↔ w.comap = v := by sorry
