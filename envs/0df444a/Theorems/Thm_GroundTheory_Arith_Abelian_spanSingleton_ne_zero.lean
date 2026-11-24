-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_spanSingleton_ne_zero
-- name    : GroundTheory.Arith.Abelian.spanSingleton_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:12.836629+00:00
-- url     : https://prove2.me/theorems/ffed7fbf-859f-4796-a730-d12b109c6788
-- title:
--   Abelian: span Singleton ne zero
-- statement:
--   The Abelian construction uses the span Singleton ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L183-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L183-L185

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
omit [IsAlgClosed F] [W.IsElliptic]

theorem GroundTheory.Arith.Abelian.spanSingleton_ne_zero {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    FractionalIdeal.spanSingleton W.toAffine.CoordinateRing⁰ f ≠ 0 := by sorry
