-- Prove2me | Theorems.Thm_Kyprianou_exercise2_5_AllPartsCh02V3
-- name    : Kyprianou.exercise2_5_AllPartsCh02V3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:27:14.360017+00:00
-- url     : https://prove2.me/theorems/1e11844e-ead4-473b-ba57-39e21eb6f1d2
-- title:
--   Exercise 2.5: Cantor inverse and a bounded cadlag path of infinite variation
-- statement:
--   Part (i) constructs the Cantor staircase through its self-similar functional equations, then its right-continuous generalised inverse with positive dense jumps and bounded variation under a linear drift; part (ii) constructs a bounded cadlag path with alternating signed dyadic jumps and infinite total variation. The printed summand J(x) was corrected to J(s).
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.5, pp. 62-66; see source-issues.json for transcription corrections

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem exercise2_5_AllPartsCh02V3 :
    (∃ (F : ℝ → ℝ),
      ContinuousOn F (Set.Icc (0 : ℝ) 1) ∧
      MonotoneOn F (Set.Icc (0 : ℝ) 1) ∧
      F 0 = 0 ∧ F 1 = 1 ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / 3),
        F x = (1 / 2 : ℝ) * F (3 * x)) ∧
      (∀ x ∈ Set.Icc (1 / 3 : ℝ) (2 / 3),
        F x = (1 / 2 : ℝ)) ∧
      (∀ x ∈ Set.Icc (2 / 3 : ℝ) 1,
        F x = (1 / 2 : ℝ) + (1 / 2 : ℝ) * F (3 * x - 2)) ∧
      let inverse : ℝ → ℝ := fun x =>
        if x < 1 then sInf
          {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧ x < F θ}
        else 1
      ∀ (a : ℝ),
        let g : ℝ → ℝ := fun x => inverse x - a * x
        (MonotoneOn g (Set.Icc (0 : ℝ) 1) ↔ a ≤ 0) ∧
        LocallyBoundedVariationOn g (Set.Icc (0 : ℝ) 1) ∧
        (∀ x ∈ Set.Icc (0 : ℝ) 1,
          ContinuousWithinAt g (Set.Icc x 1) x) ∧
        (∀ x ∈ Set.Ioc (0 : ℝ) 1, ∃ l : ℝ,
          Tendsto g (nhdsWithin x (Set.Iio x)) (nhds l) ∧
          l ≤ g x) ∧
        closure {x : ℝ |
          x ∈ Set.Icc (0 : ℝ) 1 ∧
          ∃ l : ℝ,
            Tendsto g (nhdsWithin x (Set.Iio x)) (nhds l) ∧
            l < g x} = Set.Icc (0 : ℝ) 1) ∧
    (∃ f : ℝ → ℝ,
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ 1) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1,
        ContinuousWithinAt f (Set.Icc x 1) x) ∧
      (∀ x ∈ Set.Ioc (0 : ℝ) 1,
        ∃ l : ℝ,
          Tendsto f (nhdsWithin x (Set.Iio x)) (nhds l)) ∧
      ¬ LocallyBoundedVariationOn f (Set.Icc (0 : ℝ) 1) ∧
      (∀ (n k : ℕ), 0 < n → Odd k →
        (k : ℝ) / (2 : ℝ) ^ n ≤ 1 →
        ∃ l : ℝ,
          Tendsto f
            (nhdsWithin ((k : ℝ) / (2 : ℝ) ^ n)
              (Set.Iio ((k : ℝ) / (2 : ℝ) ^ n)))
            (nhds l) ∧
          f ((k : ℝ) / (2 : ℝ) ^ n) - l =
          (if k % 4 = 1 then (1 : ℝ) / (2 : ℝ) ^ n
            else -(1 : ℝ) / (2 : ℝ) ^ n)))
      := by sorry
end Kyprianou
