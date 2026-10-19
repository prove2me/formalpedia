-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_ambientSphereLaw_isometry
-- name    : OAI.SubsphereRegression.ambientSphereLaw_isometry
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:25:07.019065+00:00
-- url     : https://prove2.me/theorems/9c26870e-17a9-48ba-9ce6-99ea99d98f3f
-- title:
--   The uniform measure on the unit sphere is invariant under orthogonal maps
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $d\ge1$ with its Borel $\sigma$-algebra and its Lebesgue measure $\lambda_E$ (the Haar measure giving the cube spanned by an orthonormal basis volume $1$). Let $S=\{x\in E:\|x\|=1\}$ be the unit sphere, and let $\sigma_E$ be the normalized surface measure on $S$: the surface measure induced by $\lambda_E$, for which a measurable $s\subseteq S$ has measure $d\cdot\lambda_E\bigl((0,1)\cdot s\bigr)$, divided by its total mass, so that $\sigma_E$ is a probability measure. Here $(0,1)\cdot s=\{cx:0<c<1,\ x\in s\}$. Write $\tilde\sigma_E$ for the image of $\sigma_E$ under the inclusion $S\hookrightarrow E$, that is, the uniform probability measure on the unit sphere regarded as a Borel measure on $E$, and $\bar B(z,r)=\{x\in E:\|x-z\|\le r\}$ for closed balls.
--
--   Let $e:E\to E$ be a linear isometric isomorphism (an orthogonal transformation). Then $e$ is measurable and preserves $\tilde\sigma_E$:
--   $$\tilde\sigma_E\bigl(e^{-1}(B)\bigr)=\tilde\sigma_E(B)\quad\text{for every Borel set }B\subseteq E,\qquad\text{i.e.}\quad e_*\tilde\sigma_E=\tilde\sigma_E .$$
--
--   Rotation and reflection invariance is the defining symmetry of the uniform distribution on the sphere. It is used to compare second moments in different directions and to show that reflections of the sphere preserve its normalized measure.
--
--   **Formalization Note** The conclusion is `MeasurePreserving e ambientSphereLaw ambientSphereLaw`, which packages measurability of $e$ with the equality of the image measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Spheres.lean#L223-L241

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

theorem OAI.SubsphereRegression.ambientSphereLaw_isometry [Nontrivial E] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving e (ambientSphereLaw (E := E)) (ambientSphereLaw (E := E)) := by sorry
