-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_genY_sq_add_weierstrassB
-- name    : GroundTheory.Arith.Abelian.genY_sq_add_weierstrassB
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:41:41.927861+00:00
-- url     : https://prove2.me/theorems/d6b9feed-ee46-4b01-8a7e-f9aaf6a4db17
-- title:
--   Abelian: gen Y sq add weierstrass B
-- statement:
--   The Abelian construction uses the gen Y sq add weierstrass B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L133-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L133-L138

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
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

theorem GroundTheory.Arith.Abelian.genY_sq_add_weierstrassB :
    genY W ^ 2 + algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) * genY W =
      algebraMap F[X] W.toAffine.FunctionField (weierstrassRHS W) := by sorry
