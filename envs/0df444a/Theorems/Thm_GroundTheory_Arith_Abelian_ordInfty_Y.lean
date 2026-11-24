-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_Y
-- name    : GroundTheory.Arith.Abelian.ordInfty_Y
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:25:13.376813+00:00
-- url     : https://prove2.me/theorems/f09bc73c-65e5-496e-8e5b-43cf47a2606a
-- title:
--   Abelian: ord Infty Y
-- statement:
--   The Abelian construction uses the ord Infty Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L142-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L142-L157

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

theorem GroundTheory.Arith.Abelian.ordInfty_Y :
    ordInfty W (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (AdjoinRoot.mk W.toAffine.polynomial X)) = -3 := by sorry
