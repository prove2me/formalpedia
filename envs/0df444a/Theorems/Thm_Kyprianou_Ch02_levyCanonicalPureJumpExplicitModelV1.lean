-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyCanonicalPureJumpExplicitModelV1
-- name    : Kyprianou.Ch02.levyCanonicalPureJumpExplicitModelV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:11:57.472798+00:00
-- url     : https://prove2.me/theorems/4eceb046-1446-4ccf-b766-382465a36227
-- title:
--   Pure-jump model with explicit characteristic integral and bounded actual jump mass
-- statement:
--   For a given drift and Lévy measure construct a genuine pure-jump process with its characteristic exponent, measurable coordinates, and an expected actual small-jump mass bounded by the truncated first moment multiplied by time.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12; LeanLevy path construction and generic Avram finite-cylinder path law.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyCanonicalPureJumpExplicitModelV1
    (a : ℝ) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    : ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure P ∧ IsLevyProcess X P ∧
        (∀ t, Measurable (X t)) ∧
        (∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (P.map (X t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) *
              (Complex.I * (((-a) * ξ : ℝ) : ℂ) +
                ∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure))) ∧
        (∀ n : ℕ,
          (∫⁻ ω, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal
          (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0) ∂P) ≤
            (n : ℝ≥0∞) *
              (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂levyMeasure)) := by
  sorry
