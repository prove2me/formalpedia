-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_exists_zsmul_ne_zero
-- name    : GroundTheory.Arith.Abelian.exists_zsmul_ne_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:52:51.177165+00:00
-- url     : https://prove2.me/theorems/ef10fbea-d207-5a4d-8576-013c91f1318c
-- title:
--   Abelian: exists zsmul ne zero
-- statement:
--   The Abelian construction uses the exists zsmul ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L164-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L164-L172

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
variable {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]

theorem GroundTheory.Arith.Abelian.exists_zsmul_ne_zero [IsSepClosed F] [DecidableEq F] {n : ℤ} (hn : n ≠ 0) :
    ∃ P : W.toAffine.Point, n • P ≠ 0 := by sorry
