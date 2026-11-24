-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_valuationInfty_ne_zero
-- name    : GroundTheory.Arith.Abelian.valuationInfty_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:33:29.147622+00:00
-- url     : https://prove2.me/theorems/789ee526-bba4-4f60-a268-03ef188c9047
-- title:
--   Abelian: valuation Infty ne zero
-- statement:
--   The Abelian construction uses the valuation Infty ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L93-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L93-L95

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

theorem GroundTheory.Arith.Abelian.valuationInfty_ne_zero {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    valuationInfty W f ≠ 0 := by sorry
