-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkInFullMeasurePartOfAAe
-- name    : Kyprianou.Ch06.firstMarkInFullMeasurePartOfAAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:00:00.592062+00:00
-- url     : https://prove2.me/theorems/c00baaf9-0f10-456e-bcc7-a7dc667c6617
-- title:
--   Chapter 6 first marked Poisson point belongs almost surely to any test set containing full A-intensity
-- statement:
--   At positive finite A-intensity, the original first-mark selector lies in A almost surely. If the measurable test mark set C omits only a zero-intensity part A\C, the already proved source zero-intensity first-mark support result shows that the first mark also avoids A\C almost surely, even at random first-arrival time. Consequently it belongs to C almost surely. Original marked Poisson and first-mark assumptions are retained without imposing A⊆C as a set.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkInFullMeasurePartOfAAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A) (hFinite : n A < ⊤) (hRate : 0 < n A)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (C : Set E) (hC : MeasurableSet C) (hNull : n (A \ C) = 0) :
    ∀ᵐ omega ∂P, firstMark omega ∈ (some '' C) := by sorry
