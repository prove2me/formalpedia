-- Prove2me | Theorems.Thm_Kyprianou_Ch01_expAscendingRenewalZeroAtom
-- name    : Kyprianou.Ch01.expAscendingRenewalZeroAtom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T00:54:48.134117+00:00
-- url     : https://prove2.me/theorems/0fe4eec0-bca0-41a1-8e2f-81395b51c41a
-- title:
--   The zeroth renewal convolution power contributes a unit atom at the origin
-- statement:
--   The zeroth convolution power is the unit Dirac mass at the origin, so its mass on [0,x] is one whenever x>=0, independently of the increment law. This supplies the initial renewal atom in Exercise 1.8(iv).
-- source:
--   Kyprianou (2006), Exercise 1.8(iv), worked solution pages 304-305

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_QueueingFundamentals_MG1_transforms
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.expAscendingRenewalZeroAtom
  (mu : Measure ℝ) (x : ℝ) (hx : 0 ≤ x) :
  ((QueueingFundamentals.MG1.convPow mu 0)
    (Set.Icc (0 : ℝ) x)).toReal = 1 := by sorry
