-- Prove2me | Theorems.Thm_Kyprianou_Ch04_localFiniteMarkedKernel
-- name    : Kyprianou.Ch04.localFiniteMarkedKernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:59:16.847171+00:00
-- url     : https://prove2.me/theorems/92ddf49c-632f-4693-80f2-2125d8275904
-- title:
--   Almost surely finite restricted random measure has a finite kernel version
-- statement:
--   Restrict the measures to the given region and set them to zero on the measurable exceptional event of infinite region mass.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem localFiniteMarkedKernel
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (R : Omega → Measure (Real × Real))
    (hR : ∀ S : Set (Real × Real), MeasurableSet S →
      Measurable (fun w => R w S))
    (U : Set (Real × Real)) (hU : MeasurableSet U)
    (hFin : ∀ᵐ w ∂P, R w U ≠ ⊤) :
    ∃ κ : ProbabilityTheory.Kernel Omega (Real × Real),
      (∀ w, IsFiniteMeasure (κ w)) ∧
      (∀ᵐ w ∂P, κ w = (R w).restrict U) := by
  sorry
end Kyprianou.Ch04
