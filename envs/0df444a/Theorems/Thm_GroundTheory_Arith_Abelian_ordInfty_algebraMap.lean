-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_algebraMap
-- name    : GroundTheory.Arith.Abelian.ordInfty_algebraMap
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:33:03.740527+00:00
-- url     : https://prove2.me/theorems/ee7555ce-05fe-492b-9829-b64372529473
-- title:
--   Abelian: ord Infty algebra Map
-- statement:
--   The Abelian construction uses the ord Infty algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L101-L104

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

theorem GroundTheory.Arith.Abelian.ordInfty_algebraMap {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) :
    ordInfty W (algebraMap _ W.toAffine.FunctionField a) =
      -((Algebra.norm F[X] a).natDegree : ℤ) := by sorry
