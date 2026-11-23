-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstPairIndepOfEveryFiniteShiftedTailCylinder
-- name    : Kyprianou.Ch01.firstPairIndepOfEveryFiniteShiftedTailCylinder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:10:44.958859+00:00
-- url     : https://prove2.me/theorems/d7569598-c254-4dc6-9a44-6e61338834aa
-- title:
--   Independence of every finite tail cylinder implies independence of the full two-stream tail
-- statement:
--   A measurable pair of real random variables is independent of an entire countable two-stream real-valued process whenever it is independent of each finite collection of tail coordinates. The proof must use the generation of the Pi measurable structure by finite cylinders, together with independence on the cylinder pi-system and a monotone-class or pi-lambda extension. It is a generic measure-theoretic result separate from the compound-Poisson driver.
-- source:
--   Mathlib countable product measurable cylinders, independence and pi-lambda extension; Kyprianou §1.3.4

import Mathlib
open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false

theorem Kyprianou.Ch01.firstPairIndepOfEveryFiniteShiftedTailCylinder
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (arrival marks : ℕ → Ω → ℝ)
    (hArrival : ∀ n : ℕ, Measurable (arrival n))
    (hMarks : ∀ n : ℕ, Measurable (marks n))
    (hFinite : ∀ I : Finset (ℕ ⊕ ℕ),
      IndepFun
        (fun w => (arrival 0 w, marks 0 w))
        (fun w (i : I) => match i.val with
          | Sum.inl n => arrival (n + 1) w
          | Sum.inr n => marks (n + 1) w) Q) :
    IndepFun
      (fun w => (arrival 0 w, marks 0 w))
      (fun w => ((fun n : ℕ => arrival (n + 1) w),
                 (fun n : ℕ => marks (n + 1) w))) Q := by
  sorry
