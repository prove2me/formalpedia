-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_sphere_observation_quasi
-- name    : OAI.NoiselessRegression.sphere_observation_quasi
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T09:36:29.815372+00:00
-- url     : https://prove2.me/theorems/14735ba9-0829-4e76-8846-8f0dcc300be7
-- title:
--   A noiseless observation of a uniformly random unit vector has an absolutely continuous law
-- statement:
--   Let $E$ be a real inner product space of finite dimension $d\ge3$ with its Borel $\sigma$-algebra, let $\mathbb S$ be its unit sphere with the uniform probability measure $\sigma$ (normalized surface measure), let $\gamma_E$ be the standard Gaussian measure on $E$, and let $\lambda_1$ be Lebesgue measure on $\mathbb R$. Consider the noiseless observation map
--   $$
--   \Phi:\mathbb S\times E\to E\times\mathbb R,\qquad\Phi(s,x)=\big(x,\langle s,x\rangle\big).
--   $$
--   Then $\Phi$ is quasi-measure-preserving from $\sigma\otimes\gamma_E$ to $\gamma_E\otimes\lambda_1$: it is measurable, and for every measurable $B\subseteq E\times\mathbb R$,
--
--   $$
--   (\gamma_E\otimes\lambda_1)(B)=0\quad\Longrightarrow\quad(\sigma\otimes\gamma_E)\big(\Phi^{-1}(B)\big)=0,
--   $$
--
--   i.e. $\Phi_{\#}(\sigma\otimes\gamma_E)\ll\gamma_E\otimes\lambda_1$.
--
--   In words: if the unknown direction $s$ is uniform on the sphere and the sample $x$ is standard Gaussian, the pair formed by the sample and its exact label $\langle s,x\rangle$ never charges a set that is null for the product of the Gaussian design measure and Lebesgue measure on labels. This lets almost-everywhere statements about a learner, formulated with respect to the reference measure $\gamma_E\otimes\lambda_1$, be transferred to the actual distribution of noiseless observations.
--
--   **Formalization Note** The conclusion is stated with Mathlib's `Measure.QuasiMeasurePreserving`, and the sphere is a subtype of $E$. The hypothesis `Nontrivial E` in the Lean statement is implied by $d\ge3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Observation.lean#L52-L78

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

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.NoiselessRegression.sphere_observation_quasi [Nontrivial E] (hd : 3 ≤ Module.finrank ℝ E) :
    Measure.QuasiMeasurePreserving
      (fun z : (Metric.sphere (0 : E) 1) × E => (z.2, ⟪z.1.val,z.2⟫))
      ((sphereLaw (E := E)).prod (stdGaussian E)) ((stdGaussian E).prod volume) := by sorry
