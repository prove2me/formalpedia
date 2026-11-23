-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_psiAt_eq
-- name    : GroundTheory.Arith.Abelian.psiAt_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:25.502808+00:00
-- url     : https://prove2.me/theorems/12c2aeeb-cfd6-42a8-a964-114008ae3126
-- title:
--   Abelian: psi At eq
-- statement:
--   The Abelian construction uses the psi At eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L111-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L111-L115

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

theorem GroundTheory.Arith.Abelian.psiAt_eq (x y : R) (n : ℤ) :
    psiAt W x y n =
      normEDS (2 * y + W.a₁ * x + W.a₃) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n := by sorry
