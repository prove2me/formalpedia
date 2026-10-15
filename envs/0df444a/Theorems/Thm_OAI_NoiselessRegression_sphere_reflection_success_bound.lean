-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_sphere_reflection_success_bound
-- name    : OAI.NoiselessRegression.sphere_reflection_success_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:36:01.947903+00:00
-- url     : https://prove2.me/theorems/d18efd08-b526-4f1e-bb95-d22c4a18c36b
-- title:
--   A set of unit vectors that meets its reflection only near the mirror has measure at most $21/32$
-- statement:
--   Let $E$ be a nontrivial real inner product space of finite dimension $d$, let $\mathbb S$ be its unit sphere, and let $\sigma$ be the uniform probability measure on $\mathbb S$ (the normalized surface measure, giving a measurable $s\subseteq\mathbb S$ the mass $\mathrm{Vol}(\{rx:0<r<1,\ x\in s\})/\mathrm{Vol}(B(0,1))$). Let $U\subseteq E$ be a linear subspace with $4\dim U\le d$, and let $R_U$ be the orthogonal reflection in $U$, namely $R_Ux=2\Pi_Ux-x$, where $\Pi_U$ is the orthogonal projection onto $U$; it maps $\mathbb S$ onto itself. Let $S\subseteq\mathbb S$ be $\sigma$-null-measurable and assume that whenever a point and its reflection both belong to $S$, they are close:
--   $$
--   s\in S\ \text{ and }\ R_Us\in S\quad\Longrightarrow\quad\|s-R_Us\|\le\tfrac15 .
--   $$
--   Then
--
--   $$
--   \sigma(S)\le\frac{21}{32}.
--   $$
--
--   In a typical application $U$ is spanned by at most $d/4$ observed sample vectors, so the unknown direction $s$ and its reflection $R_Us$ produce identical noiseless labels and hence the same estimate. If an estimate is within angle $1/10$ of both $s$ and $R_Us$, then $\|s-R_Us\|\le1/5$, so the set of directions on which the estimate succeeds satisfies the hypothesis. The theorem then caps the success probability at $21/32<2/3$.
--
--   **Formalization Note** The reflection on the sphere is `sphereIsometry U.reflection`, the restriction of Mathlib's `Submodule.reflection U` to the unit sphere, and null-measurability is with respect to `sphereLaw`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Sphere.lean#L381-L418

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
universe u
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.NoiselessRegression.sphere_reflection_success_bound [Nontrivial E] (U : Submodule ℝ E)
    (hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ E)
    (S : Set (Metric.sphere (0 : E) 1)) (hS : NullMeasurableSet S sphereLaw)
    (hsep : ∀ s ∈ S, sphereIsometry U.reflection s ∈ S →
      dist s.val (U.reflection s.val) ≤ 1/5) :
    sphereLaw S ≤ ENNReal.ofReal (21/32 : ℝ) := by sorry
