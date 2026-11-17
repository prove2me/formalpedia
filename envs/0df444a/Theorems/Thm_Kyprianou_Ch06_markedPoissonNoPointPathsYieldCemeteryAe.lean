-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonNoPointPathsYieldCemeteryAe
-- name    : Kyprianou.Ch06.markedPoissonNoPointPathsYieldCemeteryAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:45:07.530263+00:00
-- url     : https://prove2.me/theorems/746772f5-5ef5-433c-a62e-f1a46cbd02b4
-- title:
--   Chapter 6 first Poisson mark: pathwise empty clock gives cemetery mark
-- statement:
--   Under the original first A-mark admissibility rule, if the A-count process is identically zero for almost every sample path at all times, then the first A-arrival inverse clock is infinite and the first mark is the cemetery value almost surely. This is the deterministic implication needed in Lemma 6.18 at zero intensity. Its stronger all-time zero-count premise remains a genuine child obligation.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.markedPoissonNoPointPathsYieldCemeteryAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (hNoPoints : ∀ᵐ omega ∂P, ∀ t : NNReal, N omega t A = 0) :
    ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      sigma = ⊤ ∧ firstMark omega = none := by sorry
