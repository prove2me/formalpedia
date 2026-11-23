-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_psiAt_neg
-- name    : GroundTheory.Arith.Abelian.psiAt_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:13.258672+00:00
-- url     : https://prove2.me/theorems/0b5c3b8e-80ba-4c45-90f6-f1c98bca5db3
-- title:
--   Abelian: psi At neg
-- statement:
--   The Abelian construction uses the psi At neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L138-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L138-L139

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

theorem GroundTheory.Arith.Abelian.psiAt_neg (x y : R) (n : ℤ) : psiAt W x y (-n) = -psiAt W x y n := by sorry
