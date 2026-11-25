-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_valuation_primeHS
-- name    : GroundTheory.FunctionField.Place.valuation_primeHS
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:11:25.827092+00:00
-- url     : https://prove2.me/theorems/17ba2aac-a95e-4fa1-ac68-9ff517b0185e
-- title:
--   Place: valuation prime HS
-- statement:
--   The Place construction uses the valuation prime HS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceSum.lean#L249-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceSum.lean#L249-L275

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

theorem GroundTheory.FunctionField.Place.valuation_primeHS (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    (v.primeHS q).valuation K' = (v.placeOfPrime q).valuation := by sorry
