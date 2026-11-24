-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_heightOneOfNonsingular_asIdeal
-- name    : GroundTheory.Arith.Abelian.heightOneOfNonsingular_asIdeal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:25:41.115626+00:00
-- url     : https://prove2.me/theorems/484e38ce-b024-40b6-8e65-fb89ed3fe71e
-- title:
--   Abelian: height One Of Nonsingular as Ideal
-- statement:
--   The Abelian construction uses the height One Of Nonsingular as Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Divisors.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Divisors.lean#L75-L76

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Divisors
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
variable {W}

theorem GroundTheory.Arith.Abelian.heightOneOfNonsingular_asIdeal {x y : F} (h : W.toAffine.Nonsingular x y) :
    (heightOneOfNonsingular h).asIdeal = XYIdeal W.toAffine x (C y) := by sorry
