-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_XIdeal_eq_map
-- name    : GroundTheory.Arith.Abelian.XIdeal_eq_map
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:25:12.950065+00:00
-- url     : https://prove2.me/theorems/217c1930-6e56-4caa-9670-33b488034b7a
-- title:
--   Abelian: XIdeal eq map
-- statement:
--   The Abelian construction uses the XIdeal eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L22-L24

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

theorem GroundTheory.Arith.Abelian.XIdeal_eq_map (x : F) : XIdeal W.toAffine x =
    (Ideal.span {X - C x}).map (algebraMap F[X] W.toAffine.CoordinateRing) := by sorry
