-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ord_kaehlerUniformizer
-- name    : GroundTheory.Arith.SchemeCoh.ord_kaehlerUniformizer
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:57:10.318066+00:00
-- url     : https://prove2.me/theorems/46cbbae5-2ded-5c8a-969d-29ee4cd5ff83
-- title:
--   Scheme Coh: ord kaehler Uniformizer
-- statement:
--   The Scheme Coh construction uses the ord kaehler Uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L203-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L203-L204

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_KaehlerPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open GroundTheory.FunctionField KaehlerDifferential IntermediateField
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable [IsFunctionField k K]
variable [PerfectField k]

theorem GroundTheory.Arith.SchemeCoh.ord_kaehlerUniformizer (v : Place k K) : v.ord (kaehlerUniformizer v) = 1 := by sorry
