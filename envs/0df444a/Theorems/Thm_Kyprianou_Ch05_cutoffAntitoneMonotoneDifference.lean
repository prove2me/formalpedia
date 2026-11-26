-- Prove2me | Theorems.Thm_Kyprianou_Ch05_cutoffAntitoneMonotoneDifference
-- name    : Kyprianou.Ch05.cutoffAntitoneMonotoneDifference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:00:35.576265+00:00
-- url     : https://prove2.me/theorems/2637db3a-2793-5e18-be5e-2e198dd31d94
-- title:
--   A cutoff antitone tail is the difference of two monotone unit-bounded functions
-- statement:
--   A cutoff antitone tail is the difference of two monotone unit-bounded functions
-- source:
--   Kyprianou (2006), Lemma 5.5, renewal-tail estimates.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.cutoffAntitoneMonotoneDifference
    (g : Real → Real) (hg : Antitone g)
    (hn : ∀ t, 0 ≤ g t) (hb : ∀ t, g t ≤ 1) (y : Real) :
    ∃ p q : Real → Real, Monotone p ∧ Monotone q ∧
      (∀ t, 0 ≤ p t) ∧ (∀ t, p t ≤ 1) ∧
      (∀ t, 0 ≤ q t) ∧ (∀ t, q t ≤ 1) ∧
      (∀ t, (if y < t then g t else 0) = p t-q t) := by sorry
