-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_lintegral_pi_prefix
-- name    : OAI.NoiselessRegression.lintegral_pi_prefix
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T09:42:11.29077+00:00
-- url     : https://prove2.me/theorems/06fedc8c-b30a-411b-93e3-d556cb1e5512
-- title:
--   Integrating a function of the first $t$ coordinates against a product probability measure
-- statement:
--   Let $(E,\mathcal E)$ be a measurable space and $\nu$ a probability measure on it; for $n\in\mathbb N$ let $\nu^{\otimes n}$ denote the product measure on $E^n$ with the product $\sigma$-algebra. Let $t\le T$ be natural numbers and let $f:E^t\to[0,\infty]$ be measurable. Then
--
--   $$
--   \int_{E^T}f(x_1,\dots,x_t)\,d\nu^{\otimes T}(x_1,\dots,x_T)=\int_{E^t}f\,d\nu^{\otimes t}.
--   $$
--
--   Equivalently, the projection $E^T\to E^t$ onto the first $t$ coordinates pushes $\nu^{\otimes T}$ forward to $\nu^{\otimes t}$. This is used to show that an event depending only on the first $t$ of $T$ independent samples has the same probability as in the model with only $t$ samples, for instance for a sequential procedure that stops after $t$ steps.
--
--   **Formalization Note** The prefix of $x$ is `fun i => x (Fin.castLE ht i)`, the integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions, and only the measurable-space structure of $E$ is used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Stream.lean#L213-L237

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere
import Definitions.Def_OAI_Probability_GaussianRegression_Stream

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem OAI.NoiselessRegression.lintegral_pi_prefix (ν : Measure E) [IsProbabilityMeasure ν] {t T : ℕ} (ht : t ≤ T)
    (f : (Fin t → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : Fin T → E, f (fun i => x (Fin.castLE ht i)) ∂Measure.pi (fun _ => ν)) =
      ∫⁻ x, f x ∂Measure.pi (fun _ => ν) := by sorry
