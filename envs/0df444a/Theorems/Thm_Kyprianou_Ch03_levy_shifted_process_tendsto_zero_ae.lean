-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levy_shifted_process_tendsto_zero_ae
-- name    : Kyprianou.Ch03.levy_shifted_process_tendsto_zero_ae
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T11:08:43.278172+00:00
-- url     : https://prove2.me/theorems/3e31dbe1-8710-41b4-a0dd-b23d84cf7813
-- title:
--   Shifted Levy increments tend to 0 a.e. at the origin
-- statement:
--   For a Levy process X and time t, Y_u = X(t+u)-X(t) tends to 0 as u -> 0, almost surely.
-- source:
--   Kyprianou Ch.3 Blumenthal; cadlag at 0

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_DurrettProbability_Brownian
open Filter MeasureTheory ProbabilityTheory DurrettProbability
open scoped NNReal Topology
set_option autoImplicit false

namespace Kyprianou.Ch03

/-- Càdlàg Lévy paths: $Y_u = X_{t+u}-X_t \to 0$ as $u\to 0$, almost surely. -/
theorem levy_shifted_process_tendsto_zero_ae
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) :
    ∀ᵐ ω ∂P, Tendsto (fun u : NNReal => X (t + u) ω - X t ω) (nhds 0) (nhds 0) := by
  sorry

end Kyprianou.Ch03
