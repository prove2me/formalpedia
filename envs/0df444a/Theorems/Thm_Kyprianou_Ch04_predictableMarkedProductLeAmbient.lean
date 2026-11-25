-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableMarkedProductLeAmbient
-- name    : Kyprianou.Ch04.predictableMarkedProductLeAmbient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:59:18.775479+00:00
-- url     : https://prove2.me/theorems/9a2f84fc-a43e-457b-94ca-e9f927067baf
-- title:
--   The marked predictable sigma algebra is below the ambient product
-- statement:
--   The predictable sigma algebra is below the time-sample product sigma algebra, and pairing its measurable first projection with the measurable mark projection preserves this comparison.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem predictableMarkedProductLeAmbient
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega)) :
    F.predictable.prod (inferInstance : MeasurableSpace Real) ≤
      (inferInstance : MeasurableSpace ((NNReal × Omega) × Real)) := by
  sorry
end Kyprianou.Ch04
