-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isSeparable_of_D_ne_zero
-- name    : GroundTheory.Arith.SchemeCoh.isSeparable_of_D_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:40.985148+00:00
-- url     : https://prove2.me/theorems/d5292c8d-0e02-5d44-8ba3-bbe778886ee0
-- title:
--   Scheme Coh: is Separable of D ne zero
-- statement:
--   The Scheme Coh construction uses the is Separable of D ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L109-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L109-L121

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

theorem GroundTheory.Arith.SchemeCoh.isSeparable_of_D_ne_zero {z : K} (hz : D k K z ≠ 0) : Algebra.IsSeparable k⟮z⟯ K := by sorry
