-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkDisjointSetProbabilityZero
-- name    : Kyprianou.Ch06.firstMarkDisjointSetProbabilityZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:32:10.24322+00:00
-- url     : https://prove2.me/theorems/c1dd1180-0d2a-4fbf-9a12-d938059bb233
-- title:
--   Chapter 6 marked Poisson first-mark support is confined to A almost surely
-- statement:
--   Under the complete original cemetery-or-valid-mark selection convention from Chapter 6 Lemma 6.18, every first mark is either the cemetery value or lies in its stipulated marked set A almost surely. Consequently, for any set C disjoint from A, the probability of firstMark∈some(C) is zero, without any additional assumption about the mark distribution or its measurability.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkDisjointSetProbabilityZero
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
    (C : Set E) (hCA : Disjoint C A) :
    P {omega | firstMark omega ∈ (some '' C)} = 0 := by sorry
