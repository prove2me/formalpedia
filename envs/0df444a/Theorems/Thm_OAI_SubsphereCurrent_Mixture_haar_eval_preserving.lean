-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Mixture_haar_eval_preserving
-- name    : OAI.SubsphereCurrent.Mixture.haar_eval_preserving
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:10:54.694989+00:00
-- url     : https://prove2.me/theorems/24a28a82-9ce2-48a6-a40a-bf8cfb04c258
-- title:
--   The orbit map of a unit vector pushes Haar measure on $O(E)$ to the uniform sphere law
-- statement:
--   Let $E$ be a nonzero finite-dimensional real inner product space, equipped with its Borel $\sigma$-algebra. Write $O(E)$ for its orthogonal group (the compact group of linear isometries of $E$), $H_E$ for the Haar probability measure on $O(E)$, and $\sigma_E$ for the uniform (normalized rotation-invariant surface) probability measure on the unit sphere of $E$, regarded as a measure on $E$.
--
--   For every unit vector $x\in E$, the orbit map $\phi_x:O(E)\to E$, $\phi_x(U)=Ux$, is measure preserving from $(O(E),H_E)$ to $(E,\sigma_E)$: it is measurable and
--   $$
--   H_E\bigl(\{U\in O(E):\ Ux\in A\}\bigr)=\sigma_E(A)\qquad\text{for every Borel set }A\subseteq E,
--   $$
--   that is, the image measure of $H_E$ under $\phi_x$ is $\sigma_E$.
--
--   Thus a Haar-random rotation of any fixed unit vector is a uniformly random point of the sphere. This measure-theoretic form is convenient for transferring statements about uniform random directions to statements about random orthogonal maps and back.
--
--   **Formalization Note** `Orthogonal E` is `unitary (E →L[ℝ] E)` and `orthogonalLaw` is its Haar measure normalized to total mass $1$; `act u x` is $Ux$. `SubsphereRegression.ambientSphereLaw` is the image under the inclusion of the unit sphere into $E$ of the normalized measure `(volume.toSphere univ)⁻¹ • volume.toSphere`. `MeasurePreserving` bundles measurability of the map with the equality of measures.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Mixture/Haar.lean#L73-L88

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
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine
import Definitions.Def_OAI_Probability_Subsphere_Estimates_FixedPrecision
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Haar

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Mixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereCurrent.Mixture.haar_eval_preserving [Nontrivial E] {x : E} (hx : ‖x‖ = 1) :
    MeasurePreserving (fun u : Orthogonal E => act u x) orthogonalLaw
      SubsphereRegression.ambientSphereLaw := by sorry
