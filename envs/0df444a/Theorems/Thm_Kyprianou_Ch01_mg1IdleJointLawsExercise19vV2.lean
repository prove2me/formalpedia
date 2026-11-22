-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mg1IdleJointLawsExercise19vV2
-- name    : Kyprianou.Ch01.mg1IdleJointLawsExercise19vV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T14:24:39.756083+00:00
-- url     : https://prove2.me/theorems/983fa722-e7ff-4519-8de7-2928937ecfca
-- title:
--   Exercise 1.9(v): joint idle-time laws separated by busy-period termination
-- statement:
--   Recover both eventwise laws from the source: zero idle time with the first busy period infinite, and positive finite idle time with the first busy period finite.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.9(v), printed p. 31, the two joint distribution identities.

import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.mg1IdleJointLawsExercise19vV2
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hDriver : IsCompoundPoissonDriver arrival claims rate F P)
    (hPositive : F (Set.Iic (0 : ℝ)) = 0)
    (hMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hMu : (∫ x, x ∂F) = mu)
    (hOverloaded : 1 < (rate : ℝ) * mu)
    (theta : ℝ) (hTheta : 0 < theta)
    (hRoot : queueLaplaceExponent rate F theta = 0)
    (w : ℝ) (hw : 0 ≤ w) :
    let busyEnds : Set Ω :=
      {ω | ∃ t : ℝ≥0, 0 < t ∧
        w < riskSurplus arrival claims 1 0 t ω};
    (P {ω | ω ∉ busyEnds ∧
      totalIdleTime arrival claims w ω = 0}).toReal =
        1 - Real.exp (-theta * w) ∧
      ∀ x : ℝ, 0 ≤ x →
        (P {ω | ω ∈ busyEnds ∧
          (0 : ℝ≥0∞) < totalIdleTime arrival claims w ω ∧
          totalIdleTime arrival claims w ω ≤ ENNReal.ofReal x}).toReal =
        Real.exp (-theta * w) * (1 - Real.exp (-theta * x)) := by
  sorry
