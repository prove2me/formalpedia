-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalCrossingCellIffIndexV1
-- name    : Kyprianou.Ch05.renewalCrossingCellIffIndexV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T19:02:14.071375+00:00
-- url     : https://prove2.me/theorems/de847441-1825-46bb-a148-40d85e3d3e45
-- title:
--   On a monotone renewal path each crossing cell is exactly the passage event at its index
-- statement:
--   On a monotone renewal path each crossing cell is exactly the passage event at its index
-- source:
--   Kyprianou (2006), Lemma 5.5

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.renewalCrossingCellIffIndexV1
    {Omega : Type} (Z : ℕ → Omega → ℝ) (w : Omega)
    (hm : Monotone (fun n => renewalEpoch Z n w))
    (x : ℝ) (hx : 0 < x) (A B : Set ℝ) (hA2 : A ⊆ Ioi 0) (n : ℕ) :
    (renewalEpoch Z n w ∈ Icc 0 x ∧
      Z n w - (x-renewalEpoch Z n w) ∈ A ∧ x-renewalEpoch Z n w ∈ B) ↔
    (nextRenewalIndex Z x w = n+1 ∧ 0 < renewalOvershoot Z x w ∧
      renewalOvershoot Z x w ∈ A ∧ renewalUndershoot Z x w ∈ B) := by
  sorry
