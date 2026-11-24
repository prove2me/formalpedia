-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_finite_support_count
-- name    : GroundTheory.Arith.Abelian.finite_support_count
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:30:43.390236+00:00
-- url     : https://prove2.me/theorems/f9bc2bdc-c27b-4be3-90ff-5a07296058e4
-- title:
--   Abelian: finite support count
-- statement:
--   The Abelian construction uses the finite support count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L66-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L66-L70

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
variable [IsAlgClosed F] [W.IsElliptic]
omit [IsAlgClosed F] [W.IsElliptic]

theorem GroundTheory.Arith.Abelian.finite_support_count [IsDedekindDomain W.toAffine.CoordinateRing]
    (I : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) :
    (Function.support fun v : HeightOneSpectrum W.toAffine.CoordinateRing =>
      FractionalIdeal.count W.toAffine.FunctionField v I).Finite := by sorry
