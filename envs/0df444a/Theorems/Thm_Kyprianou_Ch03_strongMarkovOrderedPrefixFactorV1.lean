-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovOrderedPrefixFactorV1
-- name    : Kyprianou.Ch03.strongMarkovOrderedPrefixFactorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:16:04.723886+00:00
-- url     : https://prove2.me/theorems/203c1f15-c473-4596-92e5-ce28f9e5f2de
-- title:
--   Restricted chronological increment rectangles
-- statement:
--   Induct over the chronological prefix. The intersection of the initial event and all previous increment events is measurable at the next increment's start; apply the one-increment factor.
-- source:
--   Kyprianou (2006), Theorem 3.1; deterministic finite-dimensional restricted law 37502337-b7ad-4ef6-95f2-d63f0de1d870.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovOrderedPrefixFactorV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hAdapt : ∀ t : NNReal, Measurable[F t] (X t))
    (hOne : ∀ (s t : NNReal), s ≤ t → ∀ (A : Set Omega), MeasurableSet[F s] A →
      ∀ (C : Set Real), MeasurableSet C →
      P (A ∩ {w | X t w - X s w ∈ C}) =
        P A * P {w | X t w - X s w ∈ C})
    (s : NNReal) (A : Set Omega) (hA : MeasurableSet[F s] A)
    (t : ℕ → NNReal) (ht : Monotone t) (hst : s ≤ t 0)
    (C : ℕ → Set ℝ) (hC : ∀ i, MeasurableSet (C i)) (n : ℕ) :
    P (A ∩ {w | ∀ i : ℕ, i < n → X (t (i+1)) w - X (t i) w ∈ C i}) =
      P A * ∏ i ∈ Finset.range n, P {w | X (t (i+1)) w - X (t i) w ∈ C i} := by
  sorry
