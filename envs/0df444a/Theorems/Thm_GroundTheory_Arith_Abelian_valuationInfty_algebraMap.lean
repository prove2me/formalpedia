-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_valuationInfty_algebraMap
-- name    : GroundTheory.Arith.Abelian.valuationInfty_algebraMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:13.369086+00:00
-- url     : https://prove2.me/theorems/0c778421-2bc2-43e4-a1ac-1d9f1c27a2ce
-- title:
--   Abelian: valuation Infty algebra Map
-- statement:
--   The Abelian construction uses the valuation Infty algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L86-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L86-L88

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

theorem GroundTheory.Arith.Abelian.valuationInfty_algebraMap (a : W.toAffine.CoordinateRing) :
    valuationInfty W (algebraMap _ W.toAffine.FunctionField a) = valuationInftyCoord W a := by sorry
