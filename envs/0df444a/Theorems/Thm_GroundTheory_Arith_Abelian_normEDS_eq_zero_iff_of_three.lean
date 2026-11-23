-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_normEDS_eq_zero_iff_of_three
-- name    : GroundTheory.Arith.Abelian.normEDS_eq_zero_iff_of_three
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:51.554511+00:00
-- url     : https://prove2.me/theorems/6fac5b83-92aa-4ecf-8106-dbf109cab472
-- title:
--   Abelian: norm EDS eq zero iff of three
-- statement:
--   The Abelian construction uses the norm EDS eq zero iff of three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L17-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L17-L95

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
variable {R : Type*} [CommRing R] [IsDomain R]

theorem GroundTheory.Arith.Abelian.normEDS_eq_zero_iff_of_three {b d : R} (hb : b ≠ 0) (hd : d ≠ 0) (n : ℤ) :
    normEDS b 0 d n = 0 ↔ (3 : ℤ) ∣ n := by sorry
