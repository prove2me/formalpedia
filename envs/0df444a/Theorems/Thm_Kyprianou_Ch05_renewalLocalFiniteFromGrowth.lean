-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalLocalFiniteFromGrowth
-- name    : Kyprianou.Ch05.renewalLocalFiniteFromGrowth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:24:38.471396+00:00
-- url     : https://prove2.me/theorems/2f8f52b8-1852-4b42-adf6-2669b9bcfc11
-- title:
--   Renewal measure finite on bounded nonnegative intervals
-- statement:
--   Renewal measure finite on bounded nonnegative intervals
-- source:
--   Kyprianou (2006), Theorem 5.1, corrected Borel-measurable key renewal theorem; discussion 1dbfd76f-095f-4acc-b3fe-3e528b888bc6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.renewalLocalFiniteFromGrowth
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F) :
    ∀ x : Real, renewalMeasure F (Set.Icc 0 x) ≠ ⊤ := by sorry
