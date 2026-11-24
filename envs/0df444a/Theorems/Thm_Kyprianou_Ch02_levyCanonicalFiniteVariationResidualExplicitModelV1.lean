-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyCanonicalFiniteVariationResidualExplicitModelV1
-- name    : Kyprianou.Ch02.levyCanonicalFiniteVariationResidualExplicitModelV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:46:28.986227+00:00
-- url     : https://prove2.me/theorems/b7ea6938-6adc-4b21-961d-f286660a2996
-- title:
--   Canonical finite-variation residual model with explicit pure-jump characteristic exponent
-- statement:
--   Construct the canonical pure-jump model with explicit characteristic exponent and signed residual. Separating the explicit formula from the Chapter 1 exponent avoids importing incompatible duplicate characteristic-function declarations.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.12; canonical finite first moment model and equality of real Levy path laws.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyCanonicalFiniteVariationResidualExplicitModelV1
    (a : ℝ) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (hfin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure) :
    ∃ (Λ : Type) (mΛ : MeasurableSpace Λ),
      letI : MeasurableSpace Λ := mΛ
      ∃ (Q : Measure Λ) (Y : ℝ≥0 → Λ → ℝ) (d : ℝ),
        IsProbabilityMeasure Q ∧ IsLevyProcess Y Q ∧
        (∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (Q.map (Y t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) *
              (Complex.I * (((-a) * ξ : ℝ) : ℂ) +
                ∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure))) ∧
        (∀ᵐ ω ∂Q, ∀ T : ℝ≥0,
          Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
            |Y (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0)|) ∧
          Y T ω = d * (T : ℝ) +
            ∑' s : Set.Ioc (0 : ℝ≥0) T,
              (Y (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0))) := by
  sorry
