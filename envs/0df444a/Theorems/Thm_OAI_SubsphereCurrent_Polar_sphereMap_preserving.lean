-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Polar_sphereMap_preserving
-- name    : OAI.SubsphereCurrent.Polar.sphereMap_preserving
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:50:36.303722+00:00
-- url     : https://prove2.me/theorems/b06bc744-ecbf-481a-927d-49e1f0676f12
-- title:
--   Linear isometries preserve the normalized surface measure on the unit sphere
-- statement:
--   Let $E$ and $F$ be finite-dimensional real inner product spaces with their Borel $\sigma$-algebras and Lebesgue measures $\mathrm{vol}_E$, $\mathrm{vol}_F$ (the Haar measures giving the cube spanned by an orthonormal basis volume $1$). For such a space $X$ with unit sphere $S(X)$, the surface measure $\sigma_X$ and the normalized surface measure $\bar\sigma_X$ are given, for measurable $B\subseteq S(X)$, by
--   $$
--   \sigma_X(B)=\dim X\cdot\mathrm{vol}_X\bigl(\{\rho\,b:\ b\in B,\ 0<\rho<1\}\bigr),\qquad \bar\sigma_X=\sigma_X\bigl(S(X)\bigr)^{-1}\,\sigma_X ;
--   $$
--   when $X\neq0$, $\bar\sigma_X$ is the uniform probability measure on $S(X)$.
--
--   **Theorem.** Let $e:E\to F$ be a linear isometric isomorphism, and let $e_S:S(E)\to S(F)$ be its restriction to the unit spheres. Then $e_S$ is measurable and
--   $$
--   (e_S)_{\#}\,\bar\sigma_E=\bar\sigma_F .
--   $$
--
--   This naturality allows averages over the unit sphere of a subspace to be transported to any isometric copy of it, for instance from an abstract subspace to its image in a larger Euclidean space.
--
--   **Formalization Note** The normalized measure is `Affine.sphereLaw`, built from Mathlib's `Measure.toSphere` of `volume`, and $e_S$ is the homeomorphism `Polar.sphereMap e`; the conclusion is `MeasurePreserving`. For the zero space the sphere is empty and `sphereLaw` is the zero measure, and the statement remains true.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Geometry/Integration.lean#L153-L184

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

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Polar
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem OAI.SubsphereCurrent.Polar.sphereMap_preserving (e : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving (sphereMap e) (Affine.sphereLaw E) (Affine.sphereLaw F) := by sorry
