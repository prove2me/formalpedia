-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_ord_pow
-- name    : GroundTheory.FunctionField.Place.ord_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:19.195142+00:00
-- url     : https://prove2.me/theorems/a7c10ae4-62ba-4b46-921e-65b9f6279fb8
-- title:
--   Place: ord pow
-- statement:
--   The Place construction uses the ord pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L439-L446
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L439-L446

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

theorem GroundTheory.FunctionField.Place.ord_pow (x : K) (n : ℕ) : v.ord (x ^ n) = n * v.ord x := by sorry
