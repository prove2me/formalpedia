-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_sphere_reflection_success_bound
-- name    : OAI.SubsphereRegression.sphere_reflection_success_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:27:40.905912+00:00
-- url     : https://prove2.me/theorems/91dad79d-cecc-4df5-8df3-07318d8fec32
-- title:
--   A sphere set whose reflected pairs stay close has measure at most $21/32$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $d\ge1$ with its Borel $\sigma$-algebra and its Lebesgue measure $\lambda_E$ (the Haar measure giving the cube spanned by an orthonormal basis volume $1$). Let $S=\{x\in E:\|x\|=1\}$ be the unit sphere, and let $\sigma_E$ be the normalized surface measure on $S$: the surface measure induced by $\lambda_E$, for which a measurable $s\subseteq S$ has measure $d\cdot\lambda_E\bigl((0,1)\cdot s\bigr)$, divided by its total mass, so that $\sigma_E$ is a probability measure. Here $(0,1)\cdot s=\{cx:0<c<1,\ x\in s\}$.
--
--   Let $U\subseteq E$ be a linear subspace with $4\dim U\le\dim E$, let $P_U$ be the orthogonal projection onto $U$, and let $R_U(x)=2P_Ux-x$ be the reflection through $U$ (it fixes $U$ pointwise and negates $U^\perp$). Let $\mathcal S\subseteq S$ be a set of unit vectors that is null-measurable for $\sigma_E$, and assume that whenever both $x$ and $R_U(x)$ belong to $\mathcal S$, they are close:
--   $$x\in\mathcal S,\ R_U(x)\in\mathcal S\ \Longrightarrow\ \|x-R_U(x)\|\le\tfrac15 .$$
--   Then
--   $$\sigma_E(\mathcal S)\le\frac{21}{32}.$$
--
--   This is a two-point indistinguishability principle on the sphere. If an estimator cannot tell $x$ from its reflection $R_U(x)$ and succeeds only within a small distance, it can succeed at both points of a pair only when the pair is close. Since a low-dimensional reflection moves most unit vectors far, the success set has measure bounded away from $1$.
--
--   **Formalization Note** The reflection restricted to the sphere is `sphereIsometry U.reflection`; measurability is only required up to $\sigma_E$-null sets (`NullMeasurableSet`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Spheres.lean#L380-L417

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.sphere_reflection_success_bound [Nontrivial E] (U : Submodule ℝ E)
    (hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ E)
    (S : Set (Metric.sphere (0 : E) 1)) (hS : NullMeasurableSet S sphereLaw)
    (hsep : ∀ s ∈ S, sphereIsometry U.reflection s ∈ S →
      dist s.val (U.reflection s.val) ≤ 1/5) :
    sphereLaw S ≤ ENNReal.ofReal (21/32 : ℝ) := by sorry
