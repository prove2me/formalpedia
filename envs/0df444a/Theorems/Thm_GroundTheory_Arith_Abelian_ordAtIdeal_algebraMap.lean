-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_ordAtIdeal_algebraMap
-- name    : GroundTheory.Arith.Abelian.ordAtIdeal_algebraMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:03.563206+00:00
-- url     : https://prove2.me/theorems/6a0a2c7f-62c9-48f5-9e68-0d1b5654371e
-- title:
--   Abelian: ord At Ideal algebra Map
-- statement:
--   The Abelian construction uses the ord At Ideal algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L194-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L194-L200

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

theorem GroundTheory.Arith.Abelian.ordAtIdeal_algebraMap (v : HeightOneSpectrum W.toAffine.CoordinateRing)
    (a : W.toAffine.CoordinateRing) :
    ordAtIdeal W v (algebraMap _ W.toAffine.FunctionField a) =
      FractionalIdeal.count W.toAffine.FunctionField v
        ((Ideal.span {a} : Ideal _) :
          FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) := by sorry
