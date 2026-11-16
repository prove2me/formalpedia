-- Prove2me | Theorems.Thm_Kyprianou_Ch06_stationaryIncrementsFromMarginalLaw
-- name    : Kyprianou.Ch06.stationaryIncrementsFromMarginalLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:01:27.807987+00:00
-- url     : https://prove2.me/theorems/009afbee-6d17-4185-8674-bbaecba807b8
-- title:
--   Chapter 6 bridge: stationary increment laws imply HasStationaryIncrements
-- statement:
--   For a measurable real-valued stochastic process with almost-sure zero initial state and time-homogeneous increment distribution equal to its time-t marginal, the increments are stationary in the published ProbabilityTheory.HasStationaryIncrements sense. No pointwise zero-at-time-zero assumption is needed.
-- source:
--   Kyprianou (2006), Chapter 6 Lévy-process assumptions. Companion sound compatibility lemma for the existing Chapter 6 Draft, without changing its mathematical obligations.

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem Kyprianou.Ch06.stationaryIncrementsFromMarginalLaw
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hmeas : ∀ t : NNReal, Measurable (X t))
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hlaw : ∀ s t : NNReal,
      P.map (fun ω => X (s + t) ω - X s ω) = P.map (X t)) :
    ProbabilityTheory.HasStationaryIncrements X P := by sorry
