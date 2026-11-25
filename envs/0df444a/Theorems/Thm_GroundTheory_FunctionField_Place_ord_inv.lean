-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_ord_inv
-- name    : GroundTheory.FunctionField.Place.ord_inv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:21.752635+00:00
-- url     : https://prove2.me/theorems/eb0b653b-0774-4d53-9339-b337d68f9e8d
-- title:
--   Place: ord inv
-- statement:
--   The Place construction uses the ord inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L428-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L428-L433

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

theorem GroundTheory.FunctionField.Place.ord_inv (x : K) : v.ord x⁻¹ = -v.ord x := by sorry
