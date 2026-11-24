-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_algebraMap_X_sub_C
-- name    : GroundTheory.Arith.Abelian.algebraMap_X_sub_C
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:30:15.725701+00:00
-- url     : https://prove2.me/theorems/97b9a00d-da6c-4b87-9b80-454a894cc641
-- title:
--   Abelian: algebra Map X sub C
-- statement:
--   The Abelian construction uses the algebra Map X sub C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L18-L20

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Divisors
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
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
  IsDedekindDomain
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)

theorem GroundTheory.Arith.Abelian.algebraMap_X_sub_C (x : F) :
    algebraMap F[X] W.toAffine.CoordinateRing (X - C x) = XClass W.toAffine x := by sorry
