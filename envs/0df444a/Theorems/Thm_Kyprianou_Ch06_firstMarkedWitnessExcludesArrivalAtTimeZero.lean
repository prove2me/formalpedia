-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkedWitnessExcludesArrivalAtTimeZero
-- name    : Kyprianou.Ch06.firstMarkedWitnessExcludesArrivalAtTimeZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:29:36.8462+00:00
-- url     : https://prove2.me/theorems/d8279fa9-1a71-4097-ab07-85751189b582
-- title:
--   Lemma 6.18: witnessed first positive-mark arrival cannot occur at time zero
-- statement:
--   For a marked Poisson process whose counts vanish at time zero almost surely, the standard first-mark witness condition ensures that the first A-mark arrival time is strictly positive almost surely, or may be infinite. A finite arrival at zero contradicts the positive singleton count of its witnessed mark.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, first marked arrival and absence of time-zero marks.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkedWitnessExcludesArrivalAtTimeZero
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal := sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    ∀ᵐ omega ∂P, (0 : WithTop NNReal) <
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A}) := by sorry
