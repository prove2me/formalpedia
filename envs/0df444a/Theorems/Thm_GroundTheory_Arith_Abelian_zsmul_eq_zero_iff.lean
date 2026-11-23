-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_zsmul_eq_zero_iff
-- name    : GroundTheory.Arith.Abelian.zsmul_eq_zero_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:16.417354+00:00
-- url     : https://prove2.me/theorems/0c168d66-a8f3-410f-b144-20839945db12
-- title:
--   Abelian: zsmul eq zero iff
-- statement:
--   The Abelian construction uses the zsmul eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L550-L552
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L550-L552

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

theorem GroundTheory.Arith.Abelian.zsmul_eq_zero_iff (n : ℤ) :
    n • Point.some x₀ y₀ h₀ = 0 ↔ (W.ΨSq n).eval x₀ = 0 := by sorry
