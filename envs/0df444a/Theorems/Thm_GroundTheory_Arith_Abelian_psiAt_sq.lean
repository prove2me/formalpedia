-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_psiAt_sq
-- name    : GroundTheory.Arith.Abelian.psiAt_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:20.470671+00:00
-- url     : https://prove2.me/theorems/ea588833-e6ad-4529-bf06-193370a43273
-- title:
--   Abelian: psi At sq
-- statement:
--   The Abelian construction uses the psi At sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L146-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L146-L151

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

theorem GroundTheory.Arith.Abelian.psiAt_sq {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) :
    psiAt W x y n ^ 2 = (W.ΨSq n).eval x := by sorry
