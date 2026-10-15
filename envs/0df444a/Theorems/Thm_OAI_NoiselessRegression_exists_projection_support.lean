-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_exists_projection_support
-- name    : OAI.NoiselessRegression.exists_projection_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:30:49.598898+00:00
-- url     : https://prove2.me/theorems/4049fc1a-7e09-4fe1-a492-dddc1d1ef462
-- title:
--   Noiseless projections of the unit ball lie in a set of reference measure at most $192^d$
-- statement:
--   Let $E$ be a real inner product space of finite dimension $d$ with its Borel $\sigma$-algebra and standard Gaussian measure $\gamma_E$. On $E^m\times\mathbb R^m$ consider the reference measure $R_m=\gamma_E^{\otimes m}\otimes\lambda_m$, where $\lambda_m$ is Lebesgue measure on $\mathbb R^m$. If $m\le d$, then there is a measurable set $D\subseteq E^m\times\mathbb R^m$ such that:
--
--   1. $D$ contains every noiseless observation of a parameter in the closed unit ball, that is, $\big(A,(\langle t,A_1\rangle,\dots,\langle t,A_m\rangle)\big)\in D$ for all $A=(A_1,\dots,A_m)\in E^m$ and all $t\in E$ with $\|t\|\le1$;
--   2. $R_m(D)\le192^{d}$.
--
--   In formulas,
--
--   $$
--   \Big\{\big(A,(\langle t,A_j\rangle)_{j=1}^{m}\big):A\in E^m,\ \|t\|\le1\Big\}\subseteq D,\qquad\big(\gamma_E^{\otimes m}\otimes\lambda_m\big)(D)\le192^{d}.
--   $$
--
--   Although $R_m$ has infinite total mass, all noiseless observations of bounded parameters are confined to a set of finite reference measure, exponential in $d$ and independent of $m\le d$. Together with Hölder-type bounds $P(S)\le c\,R_m(S)^{\theta}$ for observation laws, this turns bounds for single sets into bounds summed over partitions of the observation space.
--
--   **Formalization Note** The Euclidean norm on $\mathbb R^m$ is taken through `WithLp.toLp 2`; the set constructed in the proof is `netProjectionSupport`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Support.lean#L296-L326

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
universe u
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.NoiselessRegression.exists_projection_support (m : ℕ) (hm : m ≤ Module.finrank ℝ E) :
    ∃ D : Set ((Fin m → E) × (Fin m → ℝ)), MeasurableSet D ∧
      (∀ A t, ‖t‖ ≤ 1 → (A, fun j => ⟪t, A j⟫) ∈ D) ∧
      matrixLabelReference (E := E) m D ≤ (192 : ℝ≥0∞)^(Module.finrank ℝ E) := by sorry
