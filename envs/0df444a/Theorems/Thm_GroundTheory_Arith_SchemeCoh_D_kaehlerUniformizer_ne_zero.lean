-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_D_kaehlerUniformizer_ne_zero
-- name    : GroundTheory.Arith.SchemeCoh.D_kaehlerUniformizer_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:50:07.770973+00:00
-- url     : https://prove2.me/theorems/4142d1f4-3497-41da-a1c2-83ebe48c4b3b
-- title:
--   Scheme Coh: D kaehler Uniformizer ne zero
-- statement:
--   The Scheme Coh construction uses the D kaehler Uniformizer ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L206-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L206-L207

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

theorem GroundTheory.Arith.SchemeCoh.D_kaehlerUniformizer_ne_zero (v : Place k K) : D k K (kaehlerUniformizer v) ≠ 0 := by sorry
