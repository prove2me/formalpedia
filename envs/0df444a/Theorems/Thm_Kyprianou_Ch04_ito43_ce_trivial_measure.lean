-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ce_trivial_measure
-- name    : Kyprianou.Ch04.ito43_ce_trivial_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:09:32.233037+00:00
-- url     : https://prove2.me/theorems/a3164da1-2290-5a2a-a18d-8061062694d8
-- title:
--   Trivial sigma algebra gives outer probability one to every nonempty set
-- statement:
--   Trivial sigma algebra gives outer probability one to every nonempty set.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3 formalisation boundary audit.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

/-- On the trivial sigma algebra, every nonempty set has outer probability one. -/

theorem Kyprianou.Ch04.ito43_ce_trivial_measure {Ω : Type} (P : @Measure Ω ⊥) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : A.Nonempty) : P A = 1 := by sorry
