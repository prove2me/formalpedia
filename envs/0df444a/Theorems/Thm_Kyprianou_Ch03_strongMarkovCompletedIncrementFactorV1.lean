-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovCompletedIncrementFactorV1
-- name    : Kyprianou.Ch03.strongMarkovCompletedIncrementFactorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:25:38.421363+00:00
-- url     : https://prove2.me/theorems/644435a2-4647-4f66-b573-630fc4a9a974
-- title:
--   Theorem 3.1: Completed-natural-past event factors from a single future increment; use independence of the raw natural sigma algebra and invariance under adjoining ambient null sets
-- statement:
--   Completed-natural-past event factors from a single future increment; use independence of the raw natural sigma algebra and invariance under adjoining ambient null sets
-- source:
--   Kyprianou (2006), Chapter 3 Theorem 3.1; parent 1965c746-9098-4274-8064-bb96ff53ec19.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovCompletedIncrementFactorV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F) :
    ∀ (s t : NNReal), s ≤ t → ∀ (A : Set Omega), MeasurableSet[F s] A →
      ∀ (C : Set Real), MeasurableSet C →
      P (A ∩ {w | X t w - X s w ∈ C}) =
        P A * P {w | X t w - X s w ∈ C} := by
  sorry
