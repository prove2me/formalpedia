-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkTemporalLawProperOverlap
-- name    : Kyprianou.Ch06.firstMarkTemporalLawProperOverlap
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T08:52:43.172194+00:00
-- url     : https://prove2.me/theorems/0710d2d8-4f4d-4012-9276-3aa417a4e756
-- title:
--   Chapter 6 first-mark and arrival-time joint density for proper overlapping mark test C
-- statement:
--   Source-faithful unconditional joint law for the first A-mark lying in an overlapping proper subset C and the first A arrival occurring after deterministic t. Its probability is the normalised A-intensity n(C∩A)/n(A) times first A-arrival survival. No outside cylinder is needed, isolating the substantive first-mark Poisson race and stopping-time mark distribution. Positive rate, original process and mark-selector hypotheses remain intact.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

theorem Kyprianou.Ch06.firstMarkTemporalLawProperOverlap
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
        0 < N omega (sigma.untopD 0) {x}))    (hRate : 0 < n A) (t : NNReal) (C : Set E)
    (hOverlap : ¬ Disjoint C A) (hProper : ¬ A ⊆ C)
    (hC : MeasurableSet C) :
P {omega | firstMark omega ∈ (some '' C) ∧ (t : WithTop NNReal) < sInf ((fun v : NNReal => (v : WithTop NNReal)) '' {v : NNReal | 0 < v ∧ 0 < N omega v A})} =
      (n (C ∩ A) / n A) * P {omega | (t : WithTop NNReal) < sInf ((fun v : NNReal => (v : WithTop NNReal)) '' {v : NNReal | 0 < v ∧ 0 < N omega v A})} := by sorry
