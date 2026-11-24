-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovGridPositionLawV1
-- name    : Kyprianou.Ch03.strongMarkovGridPositionLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:16:01.274329+00:00
-- url     : https://prove2.me/theorems/cf9686a4-bca9-4341-bd1b-fc19fe085d2b
-- title:
--   Restricted shifted ordered position vector law
-- statement:
--   Apply the common measurable cumulative-sum map to the two increment vector laws; telescope and use the zero initial value.
-- source:
--   Kyprianou (2006), Theorem 3.1; deterministic finite-dimensional restricted law 37502337-b7ad-4ef6-95f2-d63f0de1d870.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovGridPositionLawV1
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
      X (s+t (i.val+1)) w - X s w) (P.restrict A) =
    P A • Measure.map (fun w : Omega => fun i : Fin n =>
      X (t (i.val+1)) w) P := by
  sorry
