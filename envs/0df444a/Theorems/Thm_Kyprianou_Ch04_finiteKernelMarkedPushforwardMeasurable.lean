-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteKernelMarkedPushforwardMeasurable
-- name    : Kyprianou.Ch04.finiteKernelMarkedPushforwardMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:59:20.650633+00:00
-- url     : https://prove2.me/theorems/01206769-3668-491f-a12c-b31041134ab3
-- title:
--   Jointly marked pushforward of a pointwise finite kernel is measurable
-- statement:
--   Use measurable section evaluation for pointwise finite kernels and the measurable map inserting the sample coordinate.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteKernelMarkedPushforwardMeasurable
    {Omega : Type} [MeasurableSpace Omega]
    (κ : ProbabilityTheory.Kernel Omega (Real × Real))
    (hκ : ∀ w, IsFiniteMeasure (κ w)) :
    Measurable (fun w => Measure.map
      (fun z : Real × Real => ((z.1.toNNReal, w), z.2)) (κ w)) := by
  sorry
end Kyprianou.Ch04
