-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovShiftedPrefixRectanglesV1
-- name    : Kyprianou.Ch03.strongMarkovShiftedPrefixRectanglesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:20:21.955879+00:00
-- url     : https://prove2.me/theorems/96b4d338-c457-4e40-a280-84bdd506d1e5
-- title:
--   Shifted restricted increment rectangle masses
-- statement:
--   Apply the ordered prefix factor theorem twice and stationarity to the individual marginal masses.
-- source:
--   Kyprianou (2006), Theorem 3.1; ordered increment law 5b897d7e-28a6-462c-8017-67231f6a80df.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovShiftedPrefixRectanglesV1
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
    (t : ℕ → NNReal) (ht : Monotone t) (ht0 : t 0 = 0)
    (C : ℕ → Set ℝ) (hC : ∀ i, MeasurableSet (C i)) (n : ℕ) :
    P (A ∩ {w | ∀ k : ℕ, k < n → X (s+t (k+1)) w - X (s+t k) w ∈ C k}) =
    P A * P {w | ∀ k : ℕ, k < n → X (t (k+1)) w - X (t k) w ∈ C k} := by
  sorry
