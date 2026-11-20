-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianFirstPassageCharacteristicComplexSqrtPublic
-- name    : Kyprianou.Ch01.brownianFirstPassageCharacteristicComplexSqrtPublic
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T07:38:11.81876+00:00
-- url     : https://prove2.me/theorems/f69d91d1-8fdd-4cc2-ba3f-a474b817d2f9
-- title:
--   Characteristic function of Brownian first-passage time from the principal complex square-root Laplace boundary
-- statement:
--   Let T be the first positive-barrier upward crossing time of centred unit-variance Brownian motion, set to zero if no crossing. For every real frequency xi, show that the characteristic function of the pushforward distribution of T equals exp(-s*sqrt(-2 i xi)), with the principal complex square root. This is the analytic-continuation boundary theorem for the already proved real Laplace transform E[exp(-qT)]=exp(-s sqrt(2q)); justify continuity and dominated passage to imaginary q and measurability of the finite stopping time. This theorem does not assume the canonical stable skew exponent and does not use the target stable-parameters theorem.
-- source:
--   Kyprianou (2006), Exercise 1.10(ii), half-stable first-passage distribution via analytic continuation of Brownian Laplace transform.

import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.brownianFirstPassageCharacteristicComplexSqrtPublic
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : Kyprianou.Ch01.IsLinearBrownian P B 1 0)
    (hMeas : ∀ t : ℝ≥0, Measurable (B t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => B t ω))
    (s : ℝ) (hs : 0 < s) :
    let T : Ω → ℝ :=
      fun ω => match Kyprianou.Ch01.firstUpperPassage B s ω with
        | none => 0
        | some t => (t : ℝ);
    ∀ ξ : ℝ,
      charFun (P.map T) ξ =
        Complex.exp
          (-(s : ℂ) * Complex.sqrt ((-2 : ℂ) * Complex.I * (ξ : ℂ))) := by sorry
