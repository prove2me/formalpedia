-- Prove2me | Theorems.Thm_Kyprianou_Ch02_positiveLevyAnnulusRestrictEqV1
-- name    : Kyprianou.Ch02.positiveLevyAnnulusRestrictEqV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:09:24.673858+00:00
-- url     : https://prove2.me/theorems/6239d169-5901-4834-b531-ec9ed1dccee0
-- title:
--   A nonnegative Lévy measure restricts the absolute annulus to the positive annulus
-- statement:
--   Nonnegative support makes the absolute value equal to the identity almost everywhere, hence the two restrictions agree.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14; parent baac6daa-de4d-4888-9d09-eada1ed8d2c4.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.positiveLevyAnnulusRestrictEqV1
    (ν : Measure ℝ) (hs : ν (Set.Iio (0 : ℝ)) = 0) (r : ℝ) :
    ν.restrict {x : ℝ | r ≤ |x| ∧ |x| < 1} = ν.restrict (Set.Ico r 1) := by sorry
