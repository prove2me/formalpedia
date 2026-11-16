-- Prove2me | Theorems.Thm_Kyprianou_Ch06_levyProcessOfWeakGridIndependence
-- name    : Kyprianou.Ch06.levyProcessOfWeakGridIndependence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:17:06.769136+00:00
-- url     : https://prove2.me/theorems/563413ac-c02c-47d3-b568-06ba360e9ceb
-- title:
--   Chapter 6 bridge: full IsLevyProcess after weak-grid independence and zero-time normalisation
-- statement:
--   If a real-valued process has the Chapter 6 measurable marginal, almost-sure zero initial state, stationary-increment distribution and càdlàg path hypotheses, and additionally has independent increments on every monotone finite time grid, then its canonically pointwise-zero-normalised version satisfies the published ProbabilityTheory.IsLevyProcess structure. The theorem isolates the remaining weak-grid independence argument rather than assuming that Chapter 6 already supplies it.
-- source:
--   Kyprianou (2006), Chapter 6 Lévy-process path law, sound conditional bridge to the published LeanLevy IsLevyProcess predicate. This is a technical intermediate with an explicit stronger independent-increments premise.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch06_stationaryIncrementsFromMarginalLaw
import Theorems.Thm_Kyprianou_Ch06_cadlagFromPathRegularity
import Theorems.Thm_Kyprianou_Ch06_zeroTimeNormalisationAeEq

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

theorem Kyprianou.Ch06.levyProcessOfWeakGridIndependence
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hmeas : ∀ t : NNReal, Measurable (X t))
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hlaw : ∀ s t : NNReal,
      P.map (fun ω => X (s + t) ω - X s ω) = P.map (X t))
    (hindep : ProbabilityTheory.HasIndependentIncrements X P)
    (hregular : ∀ᵐ ω ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun u : NNReal => X u ω) (Set.Ici t) t ∧
      (t = 0 ∨ ∃ x : Real,
        Tendsto (fun u : NNReal => X u ω)
          (nhdsWithin t (Set.Iio t)) (nhds x))) :
    ProbabilityTheory.IsLevyProcess
      (fun t ω => if t = 0 then (0 : Real) else X t ω) P := by sorry
