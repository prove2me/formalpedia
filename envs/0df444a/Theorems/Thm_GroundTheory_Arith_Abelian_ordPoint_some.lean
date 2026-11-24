-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_ordPoint_some
-- name    : GroundTheory.Arith.Abelian.ordPoint_some
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:26:13.591949+00:00
-- url     : https://prove2.me/theorems/30eae82f-111b-42f3-8146-2381b90ee4df
-- title:
--   Abelian: ord Point some
-- statement:
--   The Abelian construction uses the ord Point some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L235-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L235-L236

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
variable [IsAlgClosed F] [W.IsElliptic]

theorem GroundTheory.Arith.Abelian.ordPoint_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    ordPoint W (.some x y h) = ordAtIdeal W (heightOneOfNonsingular h) := by sorry
