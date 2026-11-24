-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_finrank_coordinateRing
-- name    : GroundTheory.Arith.Abelian.finrank_coordinateRing
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:30:27.570516+00:00
-- url     : https://prove2.me/theorems/561ebd34-6e19-4040-b329-32f1df2a48d8
-- title:
--   Abelian: finrank coordinate Ring
-- statement:
--   The Abelian construction uses the finrank coordinate Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L15-L16

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

theorem GroundTheory.Arith.Abelian.finrank_coordinateRing : Module.finrank F[X] W.toAffine.CoordinateRing = 2 := by sorry
