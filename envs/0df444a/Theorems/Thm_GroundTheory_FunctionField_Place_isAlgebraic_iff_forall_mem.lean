-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_isAlgebraic_iff_forall_mem
-- name    : GroundTheory.FunctionField.Place.isAlgebraic_iff_forall_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:14.406851+00:00
-- url     : https://prove2.me/theorems/25c7318e-afc6-5efb-87e2-c3e7011a86cf
-- title:
--   Place: is Algebraic iff forall mem
-- statement:
--   The Place construction uses the is Algebraic iff forall mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBasic.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBasic.lean#L75-L79

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open Polynomial
open GroundTheory.FunctionField.Place
variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem GroundTheory.FunctionField.Place.isAlgebraic_iff_forall_mem {x : K} : IsAlgebraic k x ↔ ∀ v : Place k K, x ∈ v.ring := by sorry
