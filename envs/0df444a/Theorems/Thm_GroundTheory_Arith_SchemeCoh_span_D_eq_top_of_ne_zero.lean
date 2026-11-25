-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_span_D_eq_top_of_ne_zero
-- name    : GroundTheory.Arith.SchemeCoh.span_D_eq_top_of_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:44:27.786778+00:00
-- url     : https://prove2.me/theorems/446fafb4-5971-45f3-a9df-f1c6d2801d33
-- title:
--   Scheme Coh: span D eq top of ne zero
-- statement:
--   The Scheme Coh construction uses the span D eq top of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L102-L107

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

theorem GroundTheory.Arith.SchemeCoh.span_D_eq_top_of_ne_zero {z : K} (hz : D k K z ≠ 0) :
    Submodule.span K {D k K z} = ⊤ := by sorry
