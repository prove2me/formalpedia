-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_measurable_streamRoute
-- name    : OAI.NoiselessRegression.measurable_streamRoute
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T09:37:35.477126+00:00
-- url     : https://prove2.me/theorems/648a8044-ec3e-4044-b787-23d96e119261
-- title:
--   Measurability of the state reached by a finite-memory streaming update rule
-- statement:
--   Let $(E,\mathcal E)$ be a measurable space (only its measurable structure is used), and let $J$ be a finite set of memory states with a $\sigma$-algebra in which singletons are measurable; on a finite set this is the full power set. Let $\delta=(\delta_n)_{n\in\mathbb N}$ be a sequence of transition rules $\delta_n:J\times(E\times\mathbb R)\to J$ such that $(x,y)\mapsto\delta_n\big(j,(x,y)\big)$ is measurable for every $n\in\mathbb N$ and $j\in J$. For $n,k\in\mathbb N$ and $j\in J$, define the routing map $\mathrm{route}_{n,k}(j;\cdot):E^k\times\mathbb R^k\to J$ recursively by
--   $$
--   \mathrm{route}_{n,0}(j;x,y)=j,\qquad\mathrm{route}_{n,k+1}(j;x,y)=\mathrm{route}_{n+1,k}\Big(\delta_{n+1}\big(j,(x_1,y_1)\big);\,(x_2,\dots,x_{k+1}),\,(y_2,\dots,y_{k+1})\Big).
--   $$
--   Thus $\mathrm{route}_{n,k}(j;x,y)$ is the state reached by starting in state $j$ at time $n$ and feeding the observation pairs $(x_1,y_1),\dots,(x_k,y_k)$ one at a time to the rules $\delta_{n+1},\dots,\delta_{n+k}$. Then for all $n,k\in\mathbb N$ and $j\in J$,
--
--   $$
--   (x,y)\longmapsto\mathrm{route}_{n,k}(j;x,y)\ \text{ is a measurable map }E^k\times\mathbb R^k\to J .
--   $$
--
--   Equivalently, every event $\{(x,y):\mathrm{route}_{n,k}(j;x,y)=j'\}$, with $j'\in J$, is measurable. This models a streaming learner with finite memory that updates its state after each sample-label pair, and the result makes the probability of reaching a given state under random samples well defined.
--
--   **Formalization Note** Indices start at $0$ in Lean: the first observation is coordinate $0$, and the remaining ones are obtained with `Fin.tail`. The routing map is `streamRoute δ n k j`. The Lean statement omits the inner product structure of $E$ and requires `Fintype J` and `MeasurableSingletonClass J`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Stream.lean#L51-L66

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
theorem OAI.NoiselessRegression.measurable_streamRoute {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (n k : ℕ) (j : J) :
    Measurable (streamRoute δ n k j) := by sorry
