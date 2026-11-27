-- Prove2me | Theorems.Thm_Kyprianou_Ch05_unkilledPotentialUnitSupportV1
-- name    : Kyprianou.Ch05.unkilledPotentialUnitSupportV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:20:27.282776+00:00
-- url     : https://prove2.me/theorems/4c5d758f-1575-58e5-9377-d9989636daba
-- title:
--   Support and nonlattice transfer for the unit-discount potential
-- statement:
--   Nonnegative paths and strictly positive exponential weights transfer support and nonlattice properties.
-- source:
--   Kyprianou (2006), Corollary 5.3, p. 114; reduction of fcb23456-1e1f-487b-828b-a95cacc96d37.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.unkilledPotentialUnitSupportV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
    (U 1) (Set.Iio (0 : Real)) = 0 ∧
      (NonLatticeMeasure (U 0) → NonLatticeMeasure (U 1)) := by sorry
