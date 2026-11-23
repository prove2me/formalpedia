-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_psiAt_somos
-- name    : GroundTheory.Arith.Abelian.psiAt_somos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:16.927549+00:00
-- url     : https://prove2.me/theorems/36ccd418-3a8d-4e33-b3f2-3be69c520a4a
-- title:
--   Abelian: psi At somos
-- statement:
--   The Abelian construction uses the psi At somos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L117-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L117-L122

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

theorem GroundTheory.Arith.Abelian.psiAt_somos (x y : R) (n : ℤ) :
    psiAt W x y (n + 2) * psiAt W x y (n - 2) =
      (2 * y + W.a₁ * x + W.a₃) ^ 2 * psiAt W x y (n + 1) * psiAt W x y (n - 1) -
        W.Ψ₃.eval x * psiAt W x y n ^ 2 := by sorry
