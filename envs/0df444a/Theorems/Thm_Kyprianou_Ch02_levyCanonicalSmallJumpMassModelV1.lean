-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyCanonicalSmallJumpMassModelV1
-- name    : Kyprianou.Ch02.levyCanonicalSmallJumpMassModelV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:52:34.014362+00:00
-- url     : https://prove2.me/theorems/4fc054ee-2bb9-4eb1-8a41-d9f4886eff55
-- title:
--   Construct a Levy model with correct characteristic exponent and actual jump intensity bound
-- statement:
--   Construct a genuine real Levy process for the source triplet whose physical small-jump expected mass is bounded by the source truncated moment. Use the Poisson point family path construction and independent continuous Gaussian component, with actual jumps identified pathwise and an ENNReal Campbell bound. This is an existence statement for a concrete construction, not a universal original-process conclusion. No finite first moment assumed.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12; LeanLevy path construction and generic Avram finite-cylinder path law.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyCanonicalSmallJumpMassModelV1
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    : ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure P ∧ IsLevyProcess X P ∧
        (∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (P.map (X t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) *
              Kyprianou.Ch01.levyTripleExponent
                ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) ∧
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
