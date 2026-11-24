-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_genY_sq_add
-- name    : GroundTheory.Arith.Abelian.genY_sq_add
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:26:23.314808+00:00
-- url     : https://prove2.me/theorems/3df8a952-7da6-496a-9a22-26808f3c0adc
-- title:
--   Abelian: gen Y sq add
-- statement:
--   The Abelian construction uses the gen Y sq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L61-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L61-L68

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

theorem GroundTheory.Arith.Abelian.genY_sq_add : genY W ^ 2 + algebraMap F W.toAffine.FunctionField W.a₁ * genX W * genY W +
    algebraMap F W.toAffine.FunctionField W.a₃ * genY W = genX W ^ 3 +
      algebraMap F W.toAffine.FunctionField W.a₂ * genX W ^ 2 +
      algebraMap F W.toAffine.FunctionField W.a₄ * genX W +
      algebraMap F W.toAffine.FunctionField W.a₆ := by sorry
