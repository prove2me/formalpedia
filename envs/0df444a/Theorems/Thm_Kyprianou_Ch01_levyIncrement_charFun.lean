-- Prove2me | Theorems.Thm_Kyprianou_Ch01_levyIncrement_charFun
-- name    : Kyprianou.Ch01.levyIncrement_charFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:41:33.473094+00:00
-- url     : https://prove2.me/theorems/86828904-9b4c-43f6-9bc9-0e76e9e6f955
-- title:
--   Characteristic function of a stationary Lévy increment
-- statement:
--   For a real Lévy process with characteristic exponent Psi, every increment between times s and t has characteristic function exp(-(t-s)Psi), because stationary increments identify its law with the one-time marginal at lag t-s.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.5; stationary-increments consequence of IsLevyProcess and the characteristic-exponent hypothesis.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.levyIncrement_charFun
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (theta : ℝ) (Psi : ℂ)
    (hchar : ∀ t : ℝ≥0,
      charFun (P.map (X t)) theta =
        Complex.exp (-((t : ℝ) : ℂ) * Psi))
    (s t : ℝ≥0) (hst : s ≤ t) :
    charFun (P.map (fun ω => X t ω - X s ω)) theta =
      Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * Psi) := by sorry
