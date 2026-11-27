-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_valuationPoint_eq_exp
-- name    : GroundTheory.Arith.Abelian.valuationPoint_eq_exp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:57:00.930404+00:00
-- url     : https://prove2.me/theorems/8522fa37-fa4d-5a95-91f2-f8e41fecff39
-- title:
--   Abelian: valuation Point eq exp
-- statement:
--   The Abelian construction uses the valuation Point eq exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L238-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L238-L242

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

theorem GroundTheory.Arith.Abelian.valuationPoint_eq_exp (P : W.toAffine.Point) {f : W.toAffine.FunctionField}
    (hf : f ≠ 0) : valuationPoint W P f = exp (-ordPoint W P f) := by sorry
