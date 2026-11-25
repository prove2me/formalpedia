-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_relNorm_XYIdeal
-- name    : GroundTheory.Arith.Abelian.relNorm_XYIdeal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:26:25.418954+00:00
-- url     : https://prove2.me/theorems/bbf06056-b173-4227-9ecc-5c1d2d7aba1e
-- title:
--   Abelian: rel Norm XYIdeal
-- statement:
--   The Abelian construction uses the rel Norm XYIdeal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L34-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L34-L63

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

theorem GroundTheory.Arith.Abelian.relNorm_XYIdeal {x y : F} (h : W.toAffine.Nonsingular x y) :
    Ideal.relNorm F[X] (XYIdeal W.toAffine x (C y)) = Ideal.span {X - C x} := by sorry
