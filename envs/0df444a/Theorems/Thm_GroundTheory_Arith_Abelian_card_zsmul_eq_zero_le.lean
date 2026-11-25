-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_card_zsmul_eq_zero_le
-- name    : GroundTheory.Arith.Abelian.card_zsmul_eq_zero_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:38.340153+00:00
-- url     : https://prove2.me/theorems/b4caaeea-898c-4e62-b619-a16b2ae8ab45
-- title:
--   Abelian: card zsmul eq zero le
-- statement:
--   The Abelian construction uses the card zsmul eq zero le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L26-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L26-L75

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
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)

theorem GroundTheory.Arith.Abelian.card_zsmul_eq_zero_le {n : ℤ} (hn : E.ΨSq n ≠ 0) :
    Nat.card {P : E.toAffine.Point // n • P = 0} ≤ 1 + 2 * (E.ΨSq n).roots.toFinset.card := by sorry
