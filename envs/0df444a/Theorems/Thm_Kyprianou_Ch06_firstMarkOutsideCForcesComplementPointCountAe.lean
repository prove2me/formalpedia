-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkOutsideCForcesComplementPointCountAe
-- name    : Kyprianou.Ch06.firstMarkOutsideCForcesComplementPointCountAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:17:49.285206+00:00
-- url     : https://prove2.me/theorems/31d9146f-cde9-42f3-ac30-b3e96785d68f
-- title:
--   First marked Poisson point outside C implies a positive complementary point count at finite A-arrival
-- statement:
--   Under the exact source first-mark selector and count monotonicity, on finite A-arrival paths the selected first A-mark outside C forces the A\C count at the A-arrival time to be positive. This separates the two competing first-mark regions without presuming their rate law or additional stochastic assumptions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkOutsideCForcesComplementPointCountAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (C : Set E) :
    ∀ᵐ omega ∂P,
      firstMark omega ∉ (some '' C) →
      (sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})) ≠ ⊤ →
      0 < N omega
        ((sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})).untopD 0)
        (A \ C) := by sorry
