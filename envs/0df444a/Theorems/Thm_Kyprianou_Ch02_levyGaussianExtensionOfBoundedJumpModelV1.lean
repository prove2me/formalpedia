-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyGaussianExtensionOfBoundedJumpModelV1
-- name    : Kyprianou.Ch02.levyGaussianExtensionOfBoundedJumpModelV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:01:06.47229+00:00
-- url     : https://prove2.me/theorems/b452f181-401d-45db-af6c-339ebf492826
-- title:
--   Construct correct Gaussian-extended Levy model preserving actual small-jump mass bound
-- statement:
--   Given an explicit zero-Gaussian source-triplet model with physical expected small-jump mass bound, add an independent scaled canonical Brownian path on a product probability space. Its paths are continuous, so the physical jumps and expected mass remain exactly those of the pure jump model. Use genuine independent product Levy sum and characteristic exponent factorisation.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12; LeanLevy path construction and generic Avram finite-cylinder path law.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyGaussianExtensionOfBoundedJumpModelV1
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {A : Type} [MeasurableSpace A] (M : Measure A)
    [IsProbabilityMeasure M] (J : ℝ≥0 → A → ℝ)
    (hJ : IsLevyProcess J M) (hJm : ∀ t, Measurable (J t))
    (hJchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (M.map (J t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, 0, levyMeasure, hlevyMeasure⟩ ξ))
    (hJbound : ∀ n : ℕ,
      (∫⁻ ω : A, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal
          (if |J (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => J u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |J (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => J u ω) (s : ℝ≥0)|
           else 0) ∂M) ≤
        (n : ℝ≥0∞) *
          (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂levyMeasure))
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
