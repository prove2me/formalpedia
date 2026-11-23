-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_normEDS_zero_left_of_even
-- name    : GroundTheory.Arith.Abelian.normEDS_zero_left_of_even
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:36.451483+00:00
-- url     : https://prove2.me/theorems/961c9d42-530a-459e-a134-1413bed5894a
-- title:
--   Abelian: norm EDS zero left of even
-- statement:
--   The Abelian construction uses the norm EDS zero left of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L99-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L99-L100

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
omit [IsDomain R]

theorem GroundTheory.Arith.Abelian.normEDS_zero_left_of_even (c d : R) {n : ℤ} (hn : Even n) : normEDS 0 c d n = 0 := by sorry
