-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_sphere_projection_sq_integral
-- name    : OAI.SubsphereRegression.sphere_projection_sq_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:27:00.700586+00:00
-- url     : https://prove2.me/theorems/56e2ca8a-b8f0-4599-9eb3-e5ab9ca6e775
-- title:
--   Mean squared projection of a uniform unit vector onto a subspace
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $d\ge1$ with its Borel $\sigma$-algebra and its Lebesgue measure $\lambda_E$ (the Haar measure giving the cube spanned by an orthonormal basis volume $1$). Let $S=\{x\in E:\|x\|=1\}$ be the unit sphere, and let $\sigma_E$ be the normalized surface measure on $S$: the surface measure induced by $\lambda_E$, for which a measurable $s\subseteq S$ has measure $d\cdot\lambda_E\bigl((0,1)\cdot s\bigr)$, divided by its total mass, so that $\sigma_E$ is a probability measure. Here $(0,1)\cdot s=\{cx:0<c<1,\ x\in s\}$. Write $\tilde\sigma_E$ for the image of $\sigma_E$ under the inclusion $S\hookrightarrow E$, that is, the uniform probability measure on the unit sphere regarded as a Borel measure on $E$, and $\bar B(z,r)=\{x\in E:\|x-z\|\le r\}$ for closed balls.
--
--   Let $U\subseteq E$ be a linear subspace and $P_U$ the orthogonal projection onto $U$. Then
--   $$\int_E\|P_Ux\|^2\,d\tilde\sigma_E(x)=\frac{\dim U}{\dim E}=\frac{\dim U}{d}.$$
--
--   Equivalently, a uniformly random unit vector $X$ satisfies $\mathbb E\|P_UX\|^2=\dim U/d$: on average a uniform direction puts its squared length on a subspace in proportion to the dimension. Together with Markov's inequality this shows that a uniform unit vector is unlikely to lie close to a subspace of small dimension.
--
--   **Formalization Note** The integral is a Bochner integral of a real-valued function; $P_U$ is `U.orthogonalProjectionOnto`, and $E$ is assumed nontrivial.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Spheres.lean#L305-L321

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

theorem OAI.SubsphereRegression.sphere_projection_sq_integral [Nontrivial E] (U : Submodule ℝ E) :
    (∫ x, ‖U.orthogonalProjectionOnto x‖^2 ∂ambientSphereLaw) =
      (Module.finrank ℝ U : ℝ) / (Module.finrank ℝ E : ℝ) := by sorry
