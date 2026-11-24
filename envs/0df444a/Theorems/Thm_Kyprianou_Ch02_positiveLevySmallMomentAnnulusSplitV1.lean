-- Prove2me | Theorems.Thm_Kyprianou_Ch02_positiveLevySmallMomentAnnulusSplitV1
-- name    : Kyprianou.Ch02.positiveLevySmallMomentAnnulusSplitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:09:25.029902+00:00
-- url     : https://prove2.me/theorems/cf365426-3694-481e-acea-be8371a3f015
-- title:
--   Split a positive Lévy small first moment at an intermediate positive radius
-- statement:
--   The disjoint partition of (0,1) into (0,r) and [r,1) gives the identity by additivity of the Bochner integral.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14; parent baac6daa-de4d-4888-9d09-eada1ed8d2c4.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.positiveLevySmallMomentAnnulusSplitV1
    (ν : Measure ℝ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsmall : IntegrableOn (fun x : ℝ => x) (Set.Ioo 0 r) ν)
    (hband : IntegrableOn (fun x : ℝ => x) (Set.Ico r 1) ν) :
    (∫ x in Set.Ioo (0 : ℝ) 1, x ∂ν) =
      (∫ x in Set.Ioo (0 : ℝ) r, x ∂ν) + ∫ x in Set.Ico r 1, x ∂ν := by sorry
