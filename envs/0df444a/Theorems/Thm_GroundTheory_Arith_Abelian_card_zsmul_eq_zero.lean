-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_card_zsmul_eq_zero
-- name    : GroundTheory.Arith.Abelian.card_zsmul_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:42.57988+00:00
-- url     : https://prove2.me/theorems/750fb051-037b-47a7-b1ec-6e33857f0922
-- title:
--   Abelian: card zsmul eq zero
-- statement:
--   The Abelian construction uses the card zsmul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L181-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L181-L340

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic]

theorem GroundTheory.Arith.Abelian.card_zsmul_eq_zero {n : ℤ} (hn : (n : F) ≠ 0) :
    Nat.card {P : W.toAffine.Point // n • P = 0} = n.natAbs ^ 2 := by sorry
