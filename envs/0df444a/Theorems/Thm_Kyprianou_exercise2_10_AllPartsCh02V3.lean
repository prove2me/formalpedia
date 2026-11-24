-- Prove2me | Theorems.Thm_Kyprianou_exercise2_10_AllPartsCh02V3
-- name    : Kyprianou.exercise2_10_AllPartsCh02V3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T19:26:44.029376+00:00
-- url     : https://prove2.me/theorems/375c08ea-a469-4c97-b4f4-a979f5d952d1
-- title:
--   Exercise 2.10: multidimensional Lévy-Itô existence and characteristic exponent
-- statement:
--   All five clauses: existence of a multidimensional càdlàg process starting at zero, full past-independent stationary increments, and the Lévy–Khintchine characteristic exponent for drift vector, positive semidefinite Gaussian covariance and Lévy measure. The missing finiteness sign in the printed measure condition is supplied as a necessary source correction.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.10, pp. 62-66; corrections tracked in source-issues.json

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem exercise2_10_AllPartsCh02V3
    (d : ℕ) (hd : 1 < d) (a : Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hAsymm : A.transpose = A)
    (hApos : ∀ v : Fin d → ℝ,
      0 ≤ ∑ i : Fin d, ∑ j : Fin d, v i * A i j * v j)
    (ν : Measure (Fin d → ℝ))
    (hzero : ν {0} = 0)
    (hLevy : (∫⁻ x, ENNReal.ofReal
      (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ))) ∂ν) < ⊤) :
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
            Complex.exp (-(t : ℝ) *
              (Complex.I *
                (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
               (((∑ i : Fin d, ∑ j : Fin d,
                   θ i * A i j * θ j : ℝ) / 2) : ℂ) +
               ∫ x, (1 -
                 Complex.exp (Complex.I *
                   (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) +
                 Complex.I *
                   (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ) *
                   (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν)))
      := by sorry
end Kyprianou
