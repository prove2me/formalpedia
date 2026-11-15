-- Prove2me | Theorems.Thm_Kyprianou_Ch01_levy_khintchine_process_exists
-- name    : Kyprianou.Ch01.levy_khintchine_process_exists
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T07:50:58.716385+00:00
-- url     : https://prove2.me/theorems/19d7fcfb-35c5-4bde-9586-c6020466ee49
-- title:
--   Theorem 1.6: existence of a Lévy process from an admissible Lévy triplet
-- statement:
--   Kyprianou (2006), Theorem 1.6, printed pp. 4–5. For any admissible Lévy–Khintchine triplet, construct a genuine probability space and real-valued càdlàg stationary-independent-increment process whose characteristic function has the prescribed triplet exponent at every nonnegative time. The LeanLevy exponent uses the opposite sign convention from Kyprianou's Ψ, so the expression exp(t T.exponent) is intentional. No actual existence assertion or process property is assumed. The source book proves the result in Chapter 2 using the Lévy–Itô decomposition. Formal statement is a draft; remote compiler and definition-compatibility verification have not yet occurred.
-- source:
--   A. E. Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Theorem 1.6, printed pp. 4–5; constructive proof in Chapter 2, Theorem 2.1. Related proved Prove2Me pure-jump special case c96c705b-ce68-422d-a3b1-08f358946e6e.

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.levy_khintchine_process_exists
    (T : ProbabilityTheory.LevyKhintchineTriple) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (μ : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure μ ∧ IsLevyProcess X μ ∧
        (∀ t, Measurable (X t)) ∧
        ∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (μ.map (X t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) * Kyprianou.Ch01.levyTripleExponent T ξ) := by
  sorry
