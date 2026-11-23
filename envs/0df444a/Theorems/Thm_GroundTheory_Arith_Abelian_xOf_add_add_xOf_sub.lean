-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_xOf_add_add_xOf_sub
-- name    : GroundTheory.Arith.Abelian.xOf_add_add_xOf_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:36.048361+00:00
-- url     : https://prove2.me/theorems/0f7dad96-d7a3-4e65-ae8a-8a11fd76aa86
-- title:
--   Abelian: x Of add add x Of sub
-- statement:
--   The Abelian construction uses the x Of add add x Of sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L254-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L254-L280

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
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [DecidableEq F]

theorem GroundTheory.Arith.Abelian.xOf_add_add_xOf_sub {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    Point.some x₁ y₁ h₁ + .some x₂ y₂ h₂ ≠ 0 ∧ Point.some x₁ y₁ h₁ - .some x₂ y₂ h₂ ≠ 0 ∧
      (xOf W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) + xOf W (.some x₁ y₁ h₁ - .some x₂ y₂ h₂)) *
          (x₁ - x₂) ^ 2 =
        2 * x₁ * x₂ * (x₁ + x₂) + W.b₂ * x₁ * x₂ + W.b₄ * (x₁ + x₂) + W.b₆ := by sorry
