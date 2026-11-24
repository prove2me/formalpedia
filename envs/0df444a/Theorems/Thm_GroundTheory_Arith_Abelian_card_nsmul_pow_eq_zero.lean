-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_card_nsmul_pow_eq_zero
-- name    : GroundTheory.Arith.Abelian.card_nsmul_pow_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:27:06.083444+00:00
-- url     : https://prove2.me/theorems/104e492d-8218-4af8-a759-0abae9e90fa7
-- title:
--   Abelian: card nsmul pow eq zero
-- statement:
--   The Abelian construction uses the card nsmul pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L298-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L298-L301

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open AddSubgroup
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem GroundTheory.Arith.Abelian.card_nsmul_pow_eq_zero (hℓF : (ℓ : F) ≠ 0) (k : ℕ) :
    Nat.card {P : W.toAffine.Point // ℓ ^ k • P = 0} = (ℓ ^ k) ^ 2 := by sorry
