-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_mem_frobImage
-- name    : GroundTheory.Arith.Abelian.mem_frobImage
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:14.361642+00:00
-- url     : https://prove2.me/theorems/479af3a3-ec2e-4547-9078-1a0fe1f60ca7
-- title:
--   Abelian: mem frob Image
-- statement:
--   The Abelian construction uses the mem frob Image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L168-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L168-L172

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

theorem GroundTheory.Arith.Abelian.mem_frobImage {K : IntermediateField F E.toAffine.FunctionField}
    {z : E.toAffine.FunctionField} : z ∈ frobImage E p K ↔ ∃ g ∈ K, g ^ p = z := by sorry
