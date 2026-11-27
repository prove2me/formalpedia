-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_kaehlerOrd_smul
-- name    : GroundTheory.Arith.SchemeCoh.kaehlerOrd_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:53:32.155516+00:00
-- url     : https://prove2.me/theorems/b3085659-4c1e-4473-a068-ee2db1beef51
-- title:
--   Scheme Coh: kaehler Ord smul
-- statement:
--   The Scheme Coh construction uses the kaehler Ord smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L212-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L212-L215

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

theorem GroundTheory.Arith.SchemeCoh.kaehlerOrd_smul (v : Place k K) {f : K} (hf : f ≠ 0) {ω : Ω[K⁄k]} (hω : ω ≠ 0) :
    kaehlerOrd v (f • ω) = v.ord f + kaehlerOrd v ω := by sorry
