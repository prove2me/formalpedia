-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_sum_ramificationIdx_mul_inertiaDeg
-- name    : GroundTheory.FunctionField.Place.sum_ramificationIdx_mul_inertiaDeg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:30:39.541036+00:00
-- url     : https://prove2.me/theorems/14f4986b-f53f-4a39-a09e-f4f122e1510e
-- title:
--   Place: sum ramification Idx mul inertia Deg
-- statement:
--   The Place construction uses the sum ramification Idx mul inertia Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceSum.lean#L322-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceSum.lean#L322-L338

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
variable [IsFunctionField k K] [IsFunctionField k K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] (v : Place k K)
attribute [local instance] isDedekindDomain_closure isFractionRing_closure finite_closure
  isTorsionFree_closure

theorem GroundTheory.FunctionField.Place.sum_ramificationIdx_mul_inertiaDeg :
    ∑ w ∈ (v.finite_liesOver (K' := K')).toFinset, w.ramificationIdx v * w.inertiaDeg v =
      Module.finrank K K' := by sorry
