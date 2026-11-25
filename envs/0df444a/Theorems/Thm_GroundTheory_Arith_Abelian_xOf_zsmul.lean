-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_xOf_zsmul
-- name    : GroundTheory.Arith.Abelian.xOf_zsmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:53.354234+00:00
-- url     : https://prove2.me/theorems/408aed02-b09c-48c2-8c32-ed768fee3605
-- title:
--   Abelian: x Of zsmul
-- statement:
--   The Abelian construction uses the x Of zsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L554-L558
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L554-L558

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
  {x₀ y₀ : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)

theorem GroundTheory.Arith.Abelian.xOf_zsmul (n : ℤ) (hn : (W.ΨSq n).eval x₀ ≠ 0) :
    xOf W (n • Point.some x₀ y₀ h₀) = (W.Φ n).eval x₀ / (W.ΨSq n).eval x₀ := by sorry
