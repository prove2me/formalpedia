-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_natDegree_eq_finsum_count_of_relNorm_eq
-- name    : GroundTheory.Arith.Abelian.natDegree_eq_finsum_count_of_relNorm_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:25:46.478933+00:00
-- url     : https://prove2.me/theorems/f712ffc4-ada9-4efa-ae64-a38ebdfd7b97
-- title:
--   Abelian: nat Degree eq finsum count of rel Norm eq
-- statement:
--   The Abelian construction uses the nat Degree eq finsum count of rel Norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L84-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L84-L120

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

theorem GroundTheory.Arith.Abelian.natDegree_eq_finsum_count_of_relNorm_eq {I : Ideal W.toAffine.CoordinateRing} (hI : I ≠ 0)
    {p : F[X]} (hp : Ideal.relNorm F[X] I = Ideal.span {p}) :
    (p.natDegree : ℤ) = ∑ᶠ v : HeightOneSpectrum W.toAffine.CoordinateRing,
      FractionalIdeal.count W.toAffine.FunctionField v
        (I : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) := by sorry
