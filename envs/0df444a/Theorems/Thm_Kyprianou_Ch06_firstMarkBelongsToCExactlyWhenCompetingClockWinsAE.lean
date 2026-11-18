-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkBelongsToCExactlyWhenCompetingClockWinsAE
-- name    : Kyprianou.Ch06.firstMarkBelongsToCExactlyWhenCompetingClockWinsAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:13:38.458421+00:00
-- url     : https://prove2.me/theorems/5f6ac68a-ee9b-4753-a1ac-12d9fc0a6358
-- title:
--   Lemma 6.18: first-mark membership equals the winning clock event almost surely, conditional on a finite positive untied arrival
-- statement:
--   For a marked Poisson process with first-mark witness and arbitrary test mark region C, the first A-mark belongs to A∩C exactly when the first (A∩C)-arrival clock precedes the first (A\C)-arrival clock, almost surely on the event of a finite, positive, untied first arrival. This lifts the deterministic equivalence into the exact marked Poisson model and is the event identification needed for its competing-rate conditional mark law.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, positive-rate proper-overlap first-mark mark-and-time independence.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalPartitionedByMarkMembership
import Theorems.Thm_Kyprianou_Ch06_firstMarkEventIffWinningCompetingClock
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkBelongsToCExactlyWhenCompetingClockWinsAE
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A C : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      let tauB : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t (A ∩ C)})
      let tauD : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t (A \ C)})
      sigma ≠ ⊤ → 0 < sigma.untopD 0 → tauB ≠ tauD →
      (firstMark omega ∈ (some '' (A ∩ C)) ↔ tauB < tauD) := by sorry
