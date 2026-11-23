-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_valuation_isEquiv
-- name    : GroundTheory.FunctionField.Place.valuation_isEquiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:33.946861+00:00
-- url     : https://prove2.me/theorems/f3e93eea-584d-48d9-952d-d1b11a529d6f
-- title:
--   Place: valuation is Equiv
-- statement:
--   The Place construction uses the valuation is Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L397-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L397-L399

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IntermediateField
open scoped WithZero
open Polynomial
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
open GroundTheory.FunctionField.Place
variable {k K} (v : Place k K)
variable [IsFunctionField k K]

theorem GroundTheory.FunctionField.Place.valuation_isEquiv : v.valuation.IsEquiv v.ring.valuation := by sorry
