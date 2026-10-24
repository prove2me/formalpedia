-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_pi_normalizedSum_moments_408915f
-- name    : FunctionalInequalities.Probability.pi_normalizedSum_moments_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:35:27.173039+00:00
-- url     : https://prove2.me/theorems/b58bc493-9675-4e53-914c-2ad20dd98246
-- title:
--   Moments Of A Normalized Sum Of Independent Copies
-- statement:
--   This statement gives the first two moments of a normalized sum under a finite product measure.
--
--   Let $\mu$ be a probability measure on a measurable space $E$, and let $f:E\to\mathbb R$ satisfy $f\in L^2(\mu)$,
--   $$\int f\,d\mu=0,\qquad \int f^2\,d\mu=1.$$
--   For every integer $N>0$, the function on $E^{\operatorname{Fin}N}$ defined by
--   $$S_N(x)=\frac{\sum_{i=1}^N f(x_i)}{\sqrt N}$$
--   is in $L^2(\mu^{\otimes N})$ and satisfies
--   $$\int S_N\,d\mu^{\otimes N}=0,
--   \qquad \int S_N^2\,d\mu^{\otimes N}=1.$$
--
--   This is the standard moment calculation for normalized independent copies and is used to establish isotropy of suspension coordinates.
--
--   **Formalization Note.** The conclusion includes an explicit `MemLp` witness; the product measure is `Measure.pi` and $N>0$ is required.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Product.lean#L75-L132 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Product`, declaration `FunctionalInequalities.Probability.pi_normalizedSum_moments`; the repository is private at upload time).

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory Filter
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section MeasurableSpace
variable {E : Type*}
variable [MeasurableSpace E]

theorem FunctionalInequalities.Probability.pi_normalizedSum_moments_408915f
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
    (N : ℕ) (hN : 0 < N) :
    MemLp (fun x : Fin N → E => (∑ i, f (x i)) / Real.sqrt N) 2
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → E, (∑ i, f (x i)) / Real.sqrt N
        ∂(Measure.pi (fun _ : Fin N => μ))) = 0 ∧
      (∫ x : Fin N → E, ((∑ i, f (x i)) / Real.sqrt N) ^ 2
        ∂(Measure.pi (fun _ : Fin N => μ))) = 1 := by sorry
