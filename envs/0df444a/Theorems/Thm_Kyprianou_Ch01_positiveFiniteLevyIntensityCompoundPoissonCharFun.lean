-- Prove2me | Theorems.Thm_Kyprianou_Ch01_positiveFiniteLevyIntensityCompoundPoissonCharFun
-- name    : Kyprianou.Ch01.positiveFiniteLevyIntensityCompoundPoissonCharFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:22:10.222534+00:00
-- url     : https://prove2.me/theorems/19266f26-adad-4afa-b5fa-4a53f2e57760
-- title:
--   Genuine compound-Poisson characteristic-function realisation of any positive finite nonzero-jump Lévy intensity
-- statement:
--   A finite positive measure Λ supported away from zero and of strictly positive total mass can be normalised to a nonzero-jump probability distribution and used with a genuine compound-Poisson driver of rate Λ(ℝ). Its time-one marginal has characteristic function exp(∫(exp(i ξ x)−1)dΛ). This realises the nondegenerate case of Kyprianou Chapter 1 Exercise 1.2(ii), retaining all mark and driver conditions.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), genuine compound-Poisson law for finite Lévy jump intensities.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory Complex LevyFoundations
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.positiveFiniteLevyIntensityCompoundPoissonCharFun
    (Λ : Measure ℝ) (hfinite : Λ Set.univ < ⊤)
    (hpos : 0 < Λ Set.univ) (hzero : Λ {0} = 0) :
    ∃ (r : ℝ≥0) (ν' : Measure ℝ) (Ω' : Type)
      (_ : MeasurableSpace Ω') (μ : Measure Ω')
      (τ Y : ℕ → Ω' → ℝ),
      IsProbabilityMeasure ν' ∧
      IsProbabilityMeasure μ ∧
      0 < r ∧ ν' {0} = 0 ∧
      LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ ∧
      ∀ xi : ℝ,
        charFun (μ.map (LevyFoundations.compoundPoisson 0 τ Y (1 : ℝ))) xi =
          Complex.exp
            (∫ x : ℝ,
              (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂Λ) := by
  sorry
