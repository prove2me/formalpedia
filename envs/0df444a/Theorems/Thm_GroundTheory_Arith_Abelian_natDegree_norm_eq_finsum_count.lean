-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_natDegree_norm_eq_finsum_count
-- name    : GroundTheory.Arith.Abelian.natDegree_norm_eq_finsum_count
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:26:09.972326+00:00
-- url     : https://prove2.me/theorems/ed19a0b5-1ce1-4a5b-9d02-6239aaa85759
-- title:
--   Abelian: nat Degree norm eq finsum count
-- statement:
--   The Abelian construction uses the nat Degree norm eq finsum count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L122-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L122-L129

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

theorem GroundTheory.Arith.Abelian.natDegree_norm_eq_finsum_count {f : W.toAffine.CoordinateRing} (hf : f ≠ 0) :
    ((Algebra.norm F[X] f).natDegree : ℤ) = ∑ᶠ v : HeightOneSpectrum W.toAffine.CoordinateRing,
      FractionalIdeal.count W.toAffine.FunctionField v
        ((Ideal.span {f} : Ideal _) :
          FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) := by sorry
