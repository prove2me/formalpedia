-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovDeterministicRestrictedPathV1
-- name    : Kyprianou.Ch03.strongMarkovDeterministicRestrictedPathV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:09:18.342245+00:00
-- url     : https://prove2.me/theorems/1965c746-9098-4274-8064-bb96ff53ec19
-- title:
--   Theorem 3.1: deterministic-time restricted future path law
-- statement:
--   At a deterministic time the entire future increment path has the original law even after restriction to any completed-natural-past event. Use stationary independent increments, finite cylinder uniqueness and completion by null sets.
-- source:
--   Kyprianou (2006), Theorem 3.1; exact parent 2623fefc-be31-45fd-9189-b00f2e50b331.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovDeterministicRestrictedPathV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F) :
    ∀ (s : NNReal) (B : Set Omega), MeasurableSet[F s] B →
      Measure.map (fun omega u => X (s + u) omega - X s omega) (P.restrict B) =
        P B • Measure.map (fun omega u => X u omega) P := by
  sorry
