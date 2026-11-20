-- Prove2me | Theorems.Thm_Kyprianou_poissonRandomMeasureIntegralLaws
-- name    : Kyprianou.poissonRandomMeasureIntegralLaws
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:13:04.350646+00:00
-- url     : https://prove2.me/theorems/5526d997-4b94-4c36-ac49-b5a1e561fd2e
-- title:
--   Theorem 2.7: Poisson stochastic-integral criterion, characteristic function and moments
-- statement:
--   The Poisson random sum is almost surely absolutely convergent iff min(1,|f|) is intensity-integrable, with the exact characteristic-function, mean and second-moment formulae under their stated conditions.
-- source:
--   Kyprianou (2006), Theorem 2.7, pp. 41–43

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem poissonRandomMeasureIntegralLaws
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f) :
    ((∀ᵐ ω ∂P,
      Integrable f (ProbabilityTheory.poissonRandomMeasure K Y ω)) ↔
      Integrable (fun x => min (1 : ℝ) |f x|) m) ∧
    (Integrable (fun x => min (1 : ℝ) |f x|) m →
      ∀ ξ : ℝ,
        charFun (P.map (fun ω =>
          ∫ x, f x ∂(ProbabilityTheory.poissonRandomMeasure K Y ω))) ξ =
        Complex.exp
          (∫ x, (Complex.exp (Complex.I *
            (((ξ * f x : ℝ) : ℂ))) - 1) ∂m)) ∧
    (Integrable f m →
      (∫ ω, (∫ x, f x ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) ∂P) =
        ∫ x, f x ∂m) ∧
    ((Integrable f m ∧ MemLp f 2 m) →
      (∫ ω, (∫ x, f x ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) ^ 2 ∂P) =
          (∫ x, f x ^ 2 ∂m) + (∫ x, f x ∂m) ^ 2)
    := by sorry
end Kyprianou
