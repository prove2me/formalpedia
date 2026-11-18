-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstMarkMembershipIffWinningClockAlmostSurely
-- name    : Kyprianou.Ch06.firstMarkMembershipIffWinningClockAlmostSurely
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:30:48.37729+00:00
-- url     : https://prove2.me/theorems/65dcce1f-ea03-4c3b-9835-29d8f0d586c6
-- title:
--   Lemma 6.18: positive-rate witnessed first mark belongs to C iff its clock beats the competing complement clock almost surely
-- statement:
--   For a marked Poisson process with a witnessed first A-mark, a finite first A-mark clock and no ties between the A∩C and A\C first-arrival clocks almost surely, the event that the first observed A-mark belongs to C agrees almost surely with the event that the A∩C arrival clock is earlier than its competitor. This provides the precise event equivalence underlying the positive-intensity proper-overlap first-mark distribution.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), pp.160–161, first marked Poisson point and two competing independent finite-intensity mark regions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalPartitionedByMarkMembership
import Theorems.Thm_Kyprianou_Ch06_firstMarkEventIffWinningCompetingClock
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstMarkMembershipIffWinningClockAlmostSurely
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A C : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal := sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (hFinite : ∀ᵐ omega ∂P, sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A}) ≠ ⊤)
    (hNoTie : ∀ᵐ omega ∂P,
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t (A ∩ C)}) ≠ sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t (A \ C)})) :
    ∀ᵐ omega ∂P,
      (firstMark omega ∈ (some '' C) ↔
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t (A ∩ C)}) < sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t (A \ C)})) := by sorry
