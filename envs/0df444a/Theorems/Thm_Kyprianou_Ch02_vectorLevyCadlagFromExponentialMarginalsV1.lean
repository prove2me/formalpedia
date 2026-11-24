-- Prove2me | Theorems.Thm_Kyprianou_Ch02_vectorLevyCadlagFromExponentialMarginalsV1
-- name    : Kyprianou.Ch02.vectorLevyCadlagFromExponentialMarginalsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:13:38.408011+00:00
-- url     : https://prove2.me/theorems/31555f66-d6ce-4104-8d03-1e409ed69b38
-- title:
--   Càdlàg vector Lévy process from exponential marginal laws
-- statement:
--   If exp(-t ψ) is the characteristic function of a probability measure on R^d for every nonnegative t, then these unique laws form a weakly continuous convolution semigroup. Construct a process with these increment laws using Kolmogorov extension and a càdlàg modification; transfer independence of an increment from every finite past grid to the generated past sigma field.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.10; convolution semigroup construction of Lévy processes

import Mathlib
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem vectorLevyCadlagFromExponentialMarginalsV1
    (d : ℕ) (ψ : (Fin d → ℝ) → ℂ)
    (h :
    ∀ t : ℝ≥0, ∃ μ : Measure (Fin d → ℝ), IsProbabilityMeasure μ ∧
      ∀ θ : Fin d → ℝ,
        (∫ x, Complex.exp (Complex.I *
          (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) ∂μ) =
          Complex.exp (-(t : ℝ) * (ψ θ))) :
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ X : ℝ≥0 → Ω → (Fin d → ℝ),
          (∀ᵐ ω ∂P,
            (∀ t : ℝ≥0,
              ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t) ∧
            ∀ t : ℝ≥0, 0 < t →
              ∃ l : Fin d → ℝ,
                Tendsto (fun s => X s ω)
                  (nhdsWithin t (Set.Iio t)) (nhds l)) ∧
          (∀ᵐ ω ∂P, X 0 ω = 0) ∧
          (∀ (s t : ℝ≥0), s ≤ t →
            ProbabilityTheory.Indep
              (MeasurableSpace.comap
                (fun ω => X t ω - X s ω) inferInstance)
              (⨆ u ∈ Set.Iic s,
                MeasurableSpace.comap (X u) inferInstance) P) ∧
          (∀ (s t : ℝ≥0), s ≤ t →
            P.map (fun ω => X t ω - X s ω) =
              P.map (X (t - s))) ∧
          (∀ (t : ℝ≥0) (θ : Fin d → ℝ),
            ∫ ω, Complex.exp (Complex.I *
              (((∑ i : Fin d, θ i * X t ω i : ℝ)) : ℂ)) ∂P =
            Complex.exp (-(t : ℝ) * ψ θ)) := by sorry
end Kyprianou.Ch02
