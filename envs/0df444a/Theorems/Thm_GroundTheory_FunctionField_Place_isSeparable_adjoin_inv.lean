-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_isSeparable_adjoin_inv
-- name    : GroundTheory.FunctionField.Place.isSeparable_adjoin_inv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:25.945852+00:00
-- url     : https://prove2.me/theorems/6b8b47a3-a6d0-50a6-afda-30bf620f5f04
-- title:
--   Place: is Separable adjoin inv
-- statement:
--   The Place construction uses the is Separable adjoin inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBridge.lean#L347-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBridge.lean#L347-L349

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
open scoped IntermediateField.algebraAdjoinAdjoin
variable [IsFunctionField k K] (t : K) [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K]
attribute [local instance] isDedekindDomain_closure_adjoin isFractionRing_closure_adjoin
omit [IsFunctionField k K]

theorem GroundTheory.FunctionField.Place.isSeparable_adjoin_inv : Algebra.IsSeparable (IntermediateField.adjoin k {t⁻¹}) K := by sorry
