-- Prove2me | Theorems.Thm_Kyprianou_Ch02_stationaryIncrementsSubLinearDriftV1
-- name    : Kyprianou.Ch02.stationaryIncrementsSubLinearDriftV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T20:44:05.49522+00:00
-- url     : https://prove2.me/theorems/492c7529-bb53-43da-8fb8-e5df6063e6e5
-- title:
--   Stationary increments preserved under deterministic linear compensation
-- statement:
--   Subtracting a deterministic linear drift from a stochastic process preserves
--   stationary increments: for each s,h the drift changes both increment laws by
--   the same deterministic constant h*c. This converts the already-Proved
--   finite-region Poisson stationarity theorem to compensated finite-band
--   stationarity for Theorem 2.10.
-- source:
--   Kyprianou (2006), Chapter 2, stationary finite-band compensated Poisson increments

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem stationaryIncrementsSubLinearDriftV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (c : ℝ)
    (hstationary : ProbabilityTheory.HasStationaryIncrements X P) :
    ProbabilityTheory.HasStationaryIncrements
      (fun (t : ℝ≥0) ω => X t ω - (t : ℝ) * c) P := by sorry
end Kyprianou.Ch02
