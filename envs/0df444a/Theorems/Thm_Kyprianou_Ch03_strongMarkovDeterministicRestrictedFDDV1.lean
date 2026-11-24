-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovDeterministicRestrictedFDDV1
-- name    : Kyprianou.Ch03.strongMarkovDeterministicRestrictedFDDV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T07:31:06.59464+00:00
-- url     : https://prove2.me/theorems/37502337-b7ad-4ef6-95f2-d63f0de1d870
-- title:
--   Theorem 3.1: Restricted deterministic finite-dimensional law
-- statement:
--   Restricted deterministic finite-dimensional law from successive independent increments: sort observation times, factor increment rectangles inductively, use stationary increment laws and telescope the cumulative sums
-- source:
--   Kyprianou (2006), Chapter 3 Theorem 3.1; parent 1965c746-9098-4274-8064-bb96ff53ec19.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovDeterministicRestrictedFDDV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hAdapt : ∀ t : NNReal, Measurable[F t] (X t))
    (hOne : ∀ (s t : NNReal), s ≤ t → ∀ (A : Set Omega), MeasurableSet[F s] A →
      ∀ (C : Set Real), MeasurableSet C →
      P (A ∩ {w | X t w - X s w ∈ C}) =
        P A * P {w | X t w - X s w ∈ C}) :
    ∀ (s : NNReal) (B : Set Omega), MeasurableSet[F s] B →
      ∀ J : Finset NNReal,
        Measure.map (fun w : Omega => fun j : J =>
          X (s + (j : NNReal)) w - X s w) (P.restrict B) =
        P B • Measure.map (fun w : Omega => fun j : J => X (j : NNReal) w) P := by
  sorry
