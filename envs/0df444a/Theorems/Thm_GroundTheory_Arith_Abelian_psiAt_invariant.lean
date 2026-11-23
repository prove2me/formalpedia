-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_psiAt_invariant
-- name    : GroundTheory.Arith.Abelian.psiAt_invariant
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:36.237125+00:00
-- url     : https://prove2.me/theorems/68562eda-932a-4f80-85b7-dbfe57d1d4bf
-- title:
--   Abelian: psi At invariant
-- statement:
--   The Abelian construction uses the psi At invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L124-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L124-L131

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
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

theorem GroundTheory.Arith.Abelian.psiAt_invariant (x y : R) (n : ℤ) :
    W.Ψ₃.eval x * (psiAt W x y (n + 2) * psiAt W x y (n - 1) ^ 2 +
        psiAt W x y (n - 2) * psiAt W x y (n + 1) ^ 2) =
      ((2 * y + W.a₁ * x + W.a₃) ^ 4 + W.preΨ₄.eval x) * psiAt W x y (n - 1) *
          psiAt W x y n * psiAt W x y (n + 1) -
        (2 * y + W.a₁ * x + W.a₃) ^ 2 * W.Ψ₃.eval x * psiAt W x y n ^ 3 := by sorry
