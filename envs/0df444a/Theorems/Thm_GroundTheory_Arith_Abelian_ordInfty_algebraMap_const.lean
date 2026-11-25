-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_algebraMap_const
-- name    : GroundTheory.Arith.Abelian.ordInfty_algebraMap_const
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:57:13.499304+00:00
-- url     : https://prove2.me/theorems/6dc20b4a-9270-4863-b426-1e7ab8637af3
-- title:
--   Abelian: ord Infty algebra Map const
-- statement:
--   The Abelian construction uses the ord Infty algebra Map const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L118-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L118-L128

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

theorem GroundTheory.Arith.Abelian.ordInfty_algebraMap_const {c : F} (hc : c ≠ 0) :
    ordInfty W (algebraMap F W.toAffine.FunctionField c) = 0 := by sorry
