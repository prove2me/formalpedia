-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_psiAt_zero
-- name    : GroundTheory.Arith.Abelian.psiAt_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:37.71285+00:00
-- url     : https://prove2.me/theorems/63c6ab2b-34c6-4976-bbef-3f5d415f456f
-- title:
--   Abelian: psi At zero
-- statement:
--   The Abelian construction uses the psi At zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L133-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L133-L133

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

theorem GroundTheory.Arith.Abelian.psiAt_zero (x y : R) : psiAt W x y 0 = 0 := by sorry
