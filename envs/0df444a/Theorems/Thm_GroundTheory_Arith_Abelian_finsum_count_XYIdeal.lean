-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_finsum_count_XYIdeal
-- name    : GroundTheory.Arith.Abelian.finsum_count_XYIdeal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:25:54.646839+00:00
-- url     : https://prove2.me/theorems/2f96f273-eef3-4c72-b899-9430e5905ac1
-- title:
--   Abelian: finsum count XYIdeal
-- statement:
--   The Abelian construction uses the finsum count XYIdeal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L72-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L72-L82

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

theorem GroundTheory.Arith.Abelian.finsum_count_XYIdeal {x y : F} (h : W.toAffine.Nonsingular x y) :
    ∑ᶠ v : HeightOneSpectrum W.toAffine.CoordinateRing,
      FractionalIdeal.count W.toAffine.FunctionField v
        ((XYIdeal W.toAffine x (C y) : Ideal _) :
          FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) = 1 := by sorry
