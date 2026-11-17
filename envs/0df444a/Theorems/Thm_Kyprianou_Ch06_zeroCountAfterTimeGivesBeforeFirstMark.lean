-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroCountAfterTimeGivesBeforeFirstMark
-- name    : Kyprianou.Ch06.zeroCountAfterTimeGivesBeforeFirstMark
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:55:38.712343+00:00
-- url     : https://prove2.me/theorems/24e270d0-d411-4a69-b1d3-22b26204b3ad
-- title:
--   Chapter 6 Poisson first arrival: later zero count bounds arrival
-- statement:
--   If a nondecreasing point-count path has zero points by a deterministic time s>t, then the first positive-count arrival time is later than t. This is the independent lower sandwich ingredient for the exact first-arrival survival law of Lemma 6.18.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroCountAfterTimeGivesBeforeFirstMark
    {Omega E : Type}
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (omega : Omega)
    (hMono : Monotone (fun t : NNReal => N omega t A))
    (s t : NNReal) (hts : t < s)
    (hZero : N omega s A = 0) :
    (t : WithTop NNReal) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A}) := by sorry
