-- Prove2me | Theorems.Thm_Kyprianou_Ch05_unkilledPassageFinite_nullMeasurable
-- name    : Kyprianou.Ch05.unkilledPassageFinite_nullMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:18:32.345688+00:00
-- url     : https://prove2.me/theorems/081a0a60-e3d6-5ac9-b083-579c464f1ac6
-- title:
--   Finite passage is null measurable under the original measure
-- statement:
--   Finite passage agrees almost everywhere with a countable union of integer-time crossing events, which are null measurable.
-- source:
--   Kyprianou (2006), Exercise 5.5(i); occupation shift and zero prefactor.

import Definitions.Def_Kyprianou_Ch05_ExponentialPassageMoments
import Mathlib
import Definitions.Def_Kyprianou_Ch05_CompleteStrictPassageMarkovLaw
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05
open Classical

theorem Kyprianou.Ch05.unkilledPassageFinite_nullMeasurable
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0) (x : Real) :
    NullMeasurableSet {w : Omega | PassageFinite Y death x w} P := by
  sorry
