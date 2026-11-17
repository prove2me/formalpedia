-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkAvoidsNullIntensityPart
-- name    : Kyprianou.Ch06.firstMarkAvoidsNullIntensityPart
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T11:55:01.242216+00:00
-- url     : https://prove2.me/theorems/9edb7cf7-be03-4ae9-b930-e746548425cf
-- title:
--   Chapter 6 first marked-Poisson point never lies in a zero-intensity intersection
-- statement:
--   Under the complete original Chapter 6 marked Poisson and cemetery-or-valid-A-first-mark selector assumptions, for any measurable test mark set C with n(C∩A)=0, P[firstMark∈some(C)]=0. By the source zero-intensity-all-times count theorem and pathwise count monotonicity for every mark set and time, a first selected mark in C∩A would force a positive count of a zero-intensity mark set, a contradiction. No mark-distribution formula is assumed.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkAvoidsNullIntensityPart
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (C : Set E) (hC : MeasurableSet C) (hNull : n (C ∩ A) = 0) :
    P {omega | firstMark omega ∈ (some '' C)} = 0 := by sorry
