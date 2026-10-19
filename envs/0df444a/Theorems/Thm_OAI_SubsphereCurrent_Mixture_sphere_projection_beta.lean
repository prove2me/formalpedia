-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Mixture_sphere_projection_beta
-- name    : OAI.SubsphereCurrent.Mixture.sphere_projection_beta
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:14:24.55213+00:00
-- url     : https://prove2.me/theorems/429c1c5a-3c92-428d-af4a-c19509826f5a
-- title:
--   Squared projection of a uniform unit vector onto a $k$-dimensional subspace is $\mathrm{Beta}(k/2,(n-k)/2)$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $n$, equipped with its Borel $\sigma$-algebra, and let $\sigma_E$ be the uniform (normalized rotation-invariant surface) probability measure on the unit sphere $\{x\in E:\|x\|=1\}$, regarded as a measure on $E$. Let $V\subseteq E$ be a subspace of dimension $k$ such that both $V$ and $V^\perp$ are nonzero, i.e. $1\le k\le n-1$, and let $P_V$ be the orthogonal projection onto $V$. Then the map $x\mapsto\|P_Vx\|^2$ is measure preserving from $\sigma_E$ to the beta distribution with parameters $k/2$ and $\dim V^\perp/2=(n-k)/2$:
--   $$
--   \sigma_E\bigl(\{x\in E:\ \|P_Vx\|^2\in A\}\bigr)=\mathrm{Beta}\Bigl(\frac k2,\frac{n-k}2\Bigr)(A)\qquad\text{for every Borel set }A\subseteq\mathbb{R}.
--   $$
--   Here $\mathrm{Beta}(\alpha,\beta)$ denotes the measure on $\mathbb{R}$ with density $q^{\alpha-1}(1-q)^{\beta-1}/B(\alpha,\beta)$ on $(0,1)$ (and $0$ elsewhere) with respect to Lebesgue measure, where $B(\alpha,\beta)=\Gamma(\alpha)\Gamma(\beta)/\Gamma(\alpha+\beta)$; for positive parameters it is the beta probability distribution.
--
--   This is the classical law of the squared length of the projection of a uniformly random unit vector onto a fixed subspace. It is the exact scalar fact from which the beta-distributed coordinates of the direction and latitude laws on the sphere are computed.
--
--   **Formalization Note** The beta measure is Mathlib's `betaMeasure ((finrank V)/2) ((finrank Vᗮ)/2)`, so the second parameter is stated as $\dim V^\perp/2$, which equals $(n-k)/2$. $\sigma_E$ is `SubsphereRegression.ambientSphereLaw`, the image under the inclusion of the unit sphere of the normalized measure `(volume.toSphere univ)⁻¹ • volume.toSphere`. Nonzeroness of $V$ and $V^\perp$ is given by the instances `[Nontrivial V] [Nontrivial Vᗮ]`; the theorem also carries the section instance `[Nontrivial E]`, which these imply.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Mixture/BetaTheory.lean#L898-L915

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
import Definitions.Def_OAI_Probability_Subsphere_Mixture_BetaTheory

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Mixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem OAI.SubsphereCurrent.Mixture.sphere_projection_beta (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ] :
    MeasurePreserving (fun x : E => ‖V.orthogonalProjectionOnto x‖^2)
      SubsphereRegression.ambientSphereLaw
      (betaMeasure ((Module.finrank ℝ V : ℝ)/2) ((Module.finrank ℝ Vᗮ : ℝ)/2)) := by sorry
