-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_powAdjoin_succ_eq_top
-- name    : GroundTheory.Arith.Abelian.powAdjoin_succ_eq_top
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:48:38.241849+00:00
-- url     : https://prove2.me/theorems/79a9d108-b9db-4255-9dce-68c3f1d4b72c
-- title:
--   Abelian: pow Adjoin succ eq top
-- statement:
--   The Abelian construction uses the pow Adjoin succ eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobeniusSep.lean#L14-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobeniusSep.lean#L14-L40

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobeniusSep
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

theorem GroundTheory.Arith.Abelian.powAdjoin_succ_eq_top (M : IntermediateField F E.toAffine.FunctionField)
    (h1 : powAdjoin E p M 1 = ⊤) {a : ℕ} (ha : powAdjoin E p M a = ⊤) :
    powAdjoin E p M (a + 1) = ⊤ := by sorry
