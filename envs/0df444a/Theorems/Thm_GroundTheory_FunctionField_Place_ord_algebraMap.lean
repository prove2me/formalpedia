-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_ord_algebraMap
-- name    : GroundTheory.FunctionField.Place.ord_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:11.538811+00:00
-- url     : https://prove2.me/theorems/b4c4595e-5899-43a2-96f1-cf215e4053fc
-- title:
--   Place: ord algebra Map
-- statement:
--   The Place construction uses the ord algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L458-L459
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L458-L459

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

theorem GroundTheory.FunctionField.Place.ord_algebraMap {c : k} (hc : c ≠ 0) : v.ord (algebraMap k K c) = 0 := by sorry
