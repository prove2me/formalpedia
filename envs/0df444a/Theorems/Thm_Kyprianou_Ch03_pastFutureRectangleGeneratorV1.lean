-- Prove2me | Theorems.Thm_Kyprianou_Ch03_pastFutureRectangleGeneratorV1
-- name    : Kyprianou.Ch03.pastFutureRectangleGeneratorV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T12:34:46.631799+00:00
-- url     : https://prove2.me/theorems/a01d556a-e8a5-4066-bfe9-483d3e4039af
-- title:
--   Past-future rectangles generate the joined sigma algebra
-- statement:
--   Intersections of one event from each sigma algebra form a pi-system generating their supremum.
-- source:
--   Exercise 3.1, conditional-expectation rectangle and monotone-class argument for leaf 6a870581-0ee4-4990-b7cb-eb140983d7c6

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.pastFutureRectangleGeneratorV1
    {Omega : Type}
    (m h : MeasurableSpace Omega) :
    m ⊔ h = MeasurableSpace.generateFrom
      {S : Set Omega | ∃ B C : Set Omega, MeasurableSet[m] B ∧ MeasurableSet[h] C ∧ S = B ∩ C}
    ∧ IsPiSystem
      {S : Set Omega | ∃ B C : Set Omega, MeasurableSet[m] B ∧ MeasurableSet[h] C ∧ S = B ∩ C} := by sorry
