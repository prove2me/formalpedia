-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_measurable_streamRoute
-- name    : OAI.SubsphereRegression.measurable_streamRoute
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:32:58.854233+00:00
-- url     : https://prove2.me/theorems/d4b407fd-152b-4081-b62c-255fd3d95463
-- title:
--   Measurability of the state reached by a finite-state stream
-- statement:
--   Let $E$ be a measurable space and let $J$ be a finite set carrying a $\sigma$-algebra in which singletons are measurable; $\mathbb{R}$ carries its Borel $\sigma$-algebra. A *transition rule* is a family $\delta=(\delta_t)_{t\in\mathbb{N}}$ of maps $\delta_t:J\times(E\times\mathbb{R})\to J$, where $\delta_t(j,(x,y))$ is the state entered at time $t$ from state $j$ after reading the observation $(x,y)$. For a starting time $n\in\mathbb{N}$, a number of steps $k\in\mathbb{N}$ and an initial state $j\in J$, the *route* $R_{n,k}(j;\cdot):E^k\times\mathbb{R}^k\to J$ sends $(A,b)=\bigl((A_1,\dots,A_k),(b_1,\dots,b_k)\bigr)$ to the last state $j_k$ of the recursion
--
--   $$
--   j_0=j,\qquad j_i=\delta_{n+i}\bigl(j_{i-1},(A_i,b_i)\bigr)\quad(1\le i\le k).
--   $$
--
--   **Theorem.** If for every $t\in\mathbb{N}$ and $j\in J$ the map $(x,y)\mapsto\delta_t(j,(x,y))$ is measurable on $E\times\mathbb{R}$, then for all $n,k\in\mathbb{N}$ and $j\in J$ the route $R_{n,k}(j;\cdot)$ is measurable from $E^k\times\mathbb{R}^k$ (with the product $\sigma$-algebra) to $J$.
--
--   Routes describe the state of a finite-memory streaming algorithm after it has processed a block of labelled observations. Their measurability is needed whenever a function of the reached state is integrated against the law of the observations, as in the block decomposition of stream continuations and in success-probability bounds for such algorithms.
--
--   **Formalization Note** The route is `streamRoute δ n k j`, defined by recursion on $k$: one step at time $n+1$, followed by a route of $k-1$ steps from time $n+1$ on the tail of the observation. Coordinates are indexed by `Fin k`, so $A_1,\dots,A_k$ above are the entries $0,\dots,k-1$. No structure on $E$ beyond its $\sigma$-algebra is used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Streaming.lean#L46-L61

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem OAI.SubsphereRegression.measurable_streamRoute {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (n k : ℕ) (j : J) :
    Measurable (streamRoute δ n k j) := by sorry
