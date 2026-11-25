-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableMarkedWindowMeasurable
-- name    : Kyprianou.Ch04.predictableMarkedWindowMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:54:27.086516+00:00
-- url     : https://prove2.me/theorems/fd6c9afb-07b8-42e7-9a6c-a7cc6e9b9146
-- title:
--   Marked adapted section on a predictable time window
-- statement:
--   Restrict to the predictable time window. On its measurable subtype the sample and mark projections are measurable into the product of the past sigma algebra and the mark sigma algebra. Extend the resulting section by zero.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem predictableMarkedWindowMeasurable
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (a : NNReal) (D : Set NNReal)
    (hD : ∀ A : Set Omega, MeasurableSet[F a] A →
      MeasurableSet[F.predictable] (D ×ˢ A))
    (g : Omega × Real → ENNReal)
    (hg : Measurable[(F a).prod inferInstance] g) :
    Measurable[F.predictable.prod inferInstance]
      (fun z : (NNReal × Omega) × Real =>
        @ite ENNReal (z.1.1 ∈ D) (Classical.propDecidable _) (g (z.1.2, z.2)) 0) := by
  sorry
end Kyprianou.Ch04
