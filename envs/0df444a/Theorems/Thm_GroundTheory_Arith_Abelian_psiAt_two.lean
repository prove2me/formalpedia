-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_psiAt_two
-- name    : GroundTheory.Arith.Abelian.psiAt_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:34.40199+00:00
-- url     : https://prove2.me/theorems/7ca8f09c-475c-4630-b8ae-897941d1f783
-- title:
--   Abelian: psi At two
-- statement:
--   The Abelian construction uses the psi At two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L135-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L135-L136

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

theorem GroundTheory.Arith.Abelian.psiAt_two (x y : R) : psiAt W x y 2 = 2 * y + W.a₁ * x + W.a₃ := by sorry
