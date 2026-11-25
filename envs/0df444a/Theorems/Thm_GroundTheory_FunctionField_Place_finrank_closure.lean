-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_finrank_closure
-- name    : GroundTheory.FunctionField.Place.finrank_closure
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:11:40.618633+00:00
-- url     : https://prove2.me/theorems/cb8b3ffc-040d-4496-8497-0a201abd0fe1
-- title:
--   Place: finrank closure
-- statement:
--   The Place construction uses the finrank closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceSum.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceSum.lean#L89-L91

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
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
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
attribute [local instance low] algebraExt
attribute [local instance] isScalarTower_ext
attribute [local instance] isTorsionFree_ext
variable [IsFunctionField k K] [FiniteDimensional K K'] [Algebra.IsSeparable K K'] (v : Place k K)
omit [Algebra k K'] [IsScalarTower k K K']

theorem GroundTheory.FunctionField.Place.finrank_closure :
    Module.finrank v.ring (integralClosure v.ring K') = Module.finrank K K' := by sorry
