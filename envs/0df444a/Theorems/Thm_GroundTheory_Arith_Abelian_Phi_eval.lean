-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_Phi_eval
-- name    : GroundTheory.Arith.Abelian.Phi_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:44.076329+00:00
-- url     : https://prove2.me/theorems/05047f5b-332c-4ce4-9443-6d84df73b661
-- title:
--   Abelian: Phi eval
-- statement:
--   The Abelian construction uses the Phi eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L153-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L153-L159

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

theorem GroundTheory.Arith.Abelian.Phi_eval {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.Φ n).eval x = x * psiAt W x y n ^ 2 - psiAt W x y (n + 1) * psiAt W x y (n - 1) := by sorry
