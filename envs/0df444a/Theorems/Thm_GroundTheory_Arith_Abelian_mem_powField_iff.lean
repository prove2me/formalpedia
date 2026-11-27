-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_mem_powField_iff
-- name    : GroundTheory.Arith.Abelian.mem_powField_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:57:08.546805+00:00
-- url     : https://prove2.me/theorems/fd59a7ab-8bb6-56c7-986d-4487bb6b8178
-- title:
--   Abelian: mem pow Field iff
-- statement:
--   The Abelian construction uses the mem pow Field iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L174-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L174-L196

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]
variable [PerfectRing F p]

theorem GroundTheory.Arith.Abelian.mem_powField_iff (z : E.toAffine.FunctionField) :
    z ∈ powField E p ↔ ∃ g, g ^ p = z := by sorry
