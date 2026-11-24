-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levy_shifted_process_measurable
-- name    : Kyprianou.Ch03.levy_shifted_process_measurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T11:08:36.416173+00:00
-- url     : https://prove2.me/theorems/0f5d258f-d9b0-458c-aaa7-79bb4cbb1136
-- title:
--   Shifted Levy increments are measurable
-- statement:
--   For a Levy process X and times t,u, the map omega |-> X(t+u)(omega)-X(t)(omega) is measurable.
-- source:
--   Kyprianou Ch.3 Blumenthal; independent increments measurability

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory ProbabilityTheory DurrettProbability
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

/-- Shifted Lévy increments $Y_u = X_{t+u}-X_t$ are measurable in $\omega$. -/
theorem levy_shifted_process_measurable
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t u : NNReal) :
    Measurable (fun ω : Omega => X (t + u) ω - X t ω) := by
  sorry

end Kyprianou.Ch03
