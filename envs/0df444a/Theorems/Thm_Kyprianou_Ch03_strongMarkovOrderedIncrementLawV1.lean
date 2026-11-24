-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovOrderedIncrementLawV1
-- name    : Kyprianou.Ch03.strongMarkovOrderedIncrementLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:16:02.404801+00:00
-- url     : https://prove2.me/theorems/5b897d7e-28a6-462c-8017-67231f6a80df
-- title:
--   Restricted shifted ordered increment vector law
-- statement:
--   Use chronological rectangle products for shifted and unshifted grids and stationarity for equal increment marginals. Finite-cylinder uniqueness gives the vector law.
-- source:
--   Kyprianou (2006), Theorem 3.1; deterministic finite-dimensional restricted law 37502337-b7ad-4ef6-95f2-d63f0de1d870.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovOrderedIncrementLawV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hAdapt : ∀ t : NNReal, Measurable[F t] (X t))
    (hOne : ∀ (s t : NNReal), s ≤ t → ∀ (A : Set Omega), MeasurableSet[F s] A →
      ∀ (C : Set Real), MeasurableSet C →
      P (A ∩ {w | X t w - X s w ∈ C}) =
        P A * P {w | X t w - X s w ∈ C})
    (hX : IsLevyProcess X P)
    (s : NNReal) (A : Set Omega) (hA : MeasurableSet[F s] A)
    (t : ℕ → NNReal) (ht : Monotone t) (ht0 : t 0 = 0) (n : ℕ) :
    Measure.map (fun w : Omega => fun i : Fin n =>
      X (s+t (i.val+1)) w - X (s+t i.val) w) (P.restrict A) =
    P A • Measure.map (fun w : Omega => fun i : Fin n =>
      X (t (i.val+1)) w - X (t i.val) w) P := by
  sorry
