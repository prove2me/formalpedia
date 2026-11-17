-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkOutsideCylinderIndependenceProperOverlap
-- name    : Kyprianou.Ch06.firstMarkOutsideCylinderIndependenceProperOverlap
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T08:52:42.564392+00:00
-- url     : https://prove2.me/theorems/ffb4c306-abcc-4414-9981-4c3925a3fbad
-- title:
--   Chapter 6 first-mark and arrival-time event independent of full outside-A count cylinders
-- statement:
--   For the original Chapter 6 positive-rate marked Poisson process, prove that the joint first A-mark-in-C and first A-arrival-after-t event is independent of arbitrary finite-dimensional counting cylinders outside A, for proper overlapping C. This isolates the source spatial outside-mark independence challenge and preserves all mark, time, count and intensity quantifiers. The marginal first-mark/arrival law and standalone A-arrival outside independence are separate noncircular obligations.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

theorem Kyprianou.Ch06.firstMarkOutsideCylinderIndependenceProperOverlap
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A)
    (hFinite : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))    (hRate : 0 < n A)
    (m : Nat) (times : Fin m → NNReal)
    (B : Fin m → Set E) (counts : Fin m → Nat)
    (t : NNReal) (C : Set E)
    (hOverlap : ¬ Disjoint C A) (hProper : ¬ A ⊆ C)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤)
    (hC : MeasurableSet C) :
P {omega | firstMark omega ∈ (some '' C) ∧ (t : WithTop NNReal) < sInf ((fun v : NNReal => (v : WithTop NNReal)) '' {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧ (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
      P {omega | firstMark omega ∈ (some '' C) ∧ (t : WithTop NNReal) < sInf ((fun v : NNReal => (v : WithTop NNReal)) '' {v : NNReal | 0 < v ∧ 0 < N omega v A})} * P {omega | ∀ i : Fin m, N omega (times i) (B i) = counts i} := by sorry
