-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levy_shifted_process_shift_indep
-- name    : Kyprianou.Ch03.levy_shifted_process_shift_indep
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T11:08:42.844489+00:00
-- url     : https://prove2.me/theorems/7bab26a1-1c49-44f5-943d-7bbff09ac5f8
-- title:
--   Full shifted-path independence for Levy increments
-- statement:
--   For Levy X and t, the process Y_u=X(t+u)-X(t) has full future shifted-increment path independent of pastSigma Y s for every s>0.
-- source:
--   Kyprianou Ch.3 Blumenthal; hypothesis for germ_zero_one_of_shift_independence_ws01f

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory ProbabilityTheory DurrettProbability
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

/-- Full shifted-path independence for $Y_u = X_{t+u}-X_t$: the future increment process
after lag $s>0$ is independent of `pastSigma Y s`. -/
theorem levy_shifted_process_shift_indep
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal)
    (s : NNReal) (hs : 0 < s) :
    Indep
      (MeasurableSpace.comap
        (fun ω (u : NNReal) =>
          (X (t + (s + u)) ω - X t ω) - (X (t + s) ω - X t ω))
        MeasurableSpace.pi)
      (pastSigma (fun u ω => X (t + u) ω - X t ω) s) P := by
  sorry

end Kyprianou.Ch03
