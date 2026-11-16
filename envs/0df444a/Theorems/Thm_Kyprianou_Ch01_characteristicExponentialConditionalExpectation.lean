-- Prove2me | Theorems.Thm_Kyprianou_Ch01_characteristicExponentialConditionalExpectation
-- name    : Kyprianou.Ch01.characteristicExponentialConditionalExpectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:08:18.280383+00:00
-- url     : https://prove2.me/theorems/86f97300-e9e0-4b59-82b6-1adec079f425
-- title:
--   Levy characteristic exponential conditional martingale integral identity
-- statement:
--   For a Levy process under its natural filtration, the exponentially compensated characteristic function has unchanged integrals on every event observable by time s, for each s<=t. This is exactly the conditional-martingale component of the original Chapter 1 characteristic-exponential martingale result, retaining all original assumptions.
-- source:
--   Kyprianou (2006), Chapter 1, exponential martingale for Levy processes. Original theorem c51342f2-0731-4877-bd58-572ae2b73f89.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.characteristicExponentialConditionalExpectation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (theta : ℝ) (Psi : ℂ)
    (hchar : ∀ t : ℝ≥0,
      charFun (P.map (X t)) theta =
        Complex.exp (-((t : ℝ) : ℂ) * Psi)) :
    let M : ℝ≥0 → Ω → ℂ :=
      fun t ω =>
        Complex.exp (Complex.I * (theta : ℂ) * (X t ω : ℂ) +
          ((t : ℝ) : ℂ) * Psi)
    ∀ (s t : ℝ≥0), s ≤ t →
      ∀ A : Set Ω,
        @MeasurableSet Ω (naturalSigma X s) A →
          (∫ ω in A, M t ω ∂P) =
            (∫ ω in A, M s ω ∂P) := by
  sorry
