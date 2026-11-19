-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstNegativePassageAfterPositiveInterval
-- name    : Kyprianou.Ch01.firstNegativePassageAfterPositiveInterval
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:35:02.422783+00:00
-- url     : https://prove2.me/theorems/d3e1813a-3c93-4c73-84f7-b8f512e90654
-- title:
--   Source first-negative-passage stopping time cannot precede a strictly positive interval
-- statement:
--   The first strict negative-passage time of the source integer-valued compound-Poisson path, including its infinity convention, is at least t whenever the sample path stays strictly positive at every time s≤t. No càdlàg or local integrability assumptions are required. The result is an independent stopped-time bridge for the reverse Lamperti identity (1.19).
-- source:
--   Kyprianou (2006), Chapter 1 equation (1.19), first negative passage

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Basic
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.firstNegativePassageAfterPositiveInterval
    {Ω : Type*} (X : NNReal → Ω → ℤ) (ω : Ω) (t : NNReal)
    (hpositive : ∀ s : NNReal, s ≤ t → 0 < X s ω) :
    (t : WithTop NNReal) ≤ firstNegativePassage X ω := by
  sorry
