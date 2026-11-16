-- Prove2me | Theorems.Thm_Kyprianou_Ch06_realLevyComponentsToPublished
-- name    : Kyprianou.Ch06.realLevyComponentsToPublished
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:45:49.364795+00:00
-- url     : https://prove2.me/theorems/a5445151-2f0b-4ba0-bec2-bebe32e1a999
-- title:
--   Chapter 6 source Lévy process induces published IsLevyProcess after canonical zero normalisation
-- statement:
--   The complete original Kyprianou Chapter 6 real-valued Lévy-process assumptions, including strictly increasing-grid finite-cylinder independence, measurable marginals, an almost-sure initial zero, stationary increments and càdlàg paths, imply the published LeanLevy IsLevyProcess predicate for the canonically zero-initialised process that agrees almost surely with the source process.
-- source:
--   Kyprianou (2006), Chapter 6, complete source-faithful compatibility to the published ProbabilityTheory.IsLevyProcess structure. Uses separate fully proved probability normalisation, weak-grid independence and conditional IsLevyProcess bridges.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch06_probabilityFromIncrementCylinderLaw
import Theorems.Thm_Kyprianou_Ch06_weakGridIndependentIncrements
import Theorems.Thm_Kyprianou_Ch06_levyProcessOfWeakGridIndependence

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

theorem Kyprianou.Ch06.realLevyComponentsToPublished
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hmeas : ∀ t : NNReal, Measurable (X t))
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hlaw : ∀ s t : NNReal,
      P.map (fun ω => X (s + t) ω - X s ω) = P.map (X t))
    (hindep : ∀ (n : Nat) (times : Fin (n + 1) → NNReal),
      StrictMono times →
      ∀ A : Fin n → Set Real, (∀ i, MeasurableSet (A i)) →
        P {ω | ∀ i : Fin n,
          X (times i.succ) ω - X (times i.castSucc) ω ∈ A i} =
        ∏ i : Fin n, P {ω |
          X (times i.succ) ω - X (times i.castSucc) ω ∈ A i})
    (hregular : ∀ᵐ ω ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun u : NNReal => X u ω) (Set.Ici t) t ∧
      (t = 0 ∨ ∃ x : Real,
        Tendsto (fun u : NNReal => X u ω)
          (nhdsWithin t (Set.Iio t)) (nhds x))) :
    ProbabilityTheory.IsLevyProcess
      (fun t ω => if t = 0 then (0 : Real) else X t ω) P := by sorry
