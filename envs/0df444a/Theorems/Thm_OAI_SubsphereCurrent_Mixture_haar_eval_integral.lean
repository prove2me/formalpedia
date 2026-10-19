-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Mixture_haar_eval_integral
-- name    : OAI.SubsphereCurrent.Mixture.haar_eval_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:09:33.296322+00:00
-- url     : https://prove2.me/theorems/0ce22235-d808-4783-9c8a-03a310555ea3
-- title:
--   Haar orbit integrals of a unit vector equal integrals over the uniform sphere law
-- statement:
--   Let $E$ be a nonzero finite-dimensional real inner product space, equipped with its Borel $\sigma$-algebra. Write $O(E)$ for its orthogonal group (the compact group of linear isometries $U:E\to E$), $H_E$ for the Haar probability measure on $O(E)$, and $\sigma_E$ for the uniform (normalized rotation-invariant surface) probability measure on the unit sphere $\{y\in E:\|y\|=1\}$, regarded as a measure on $E$.
--
--   For every unit vector $x\in E$ and every measurable function $f:E\to[0,\infty]$,
--   $$
--   \int_{O(E)} f(Ux)\,dH_E(U)=\int_E f(y)\,d\sigma_E(y).
--   $$
--
--   In words: applying a Haar-random orthogonal transformation to a fixed unit vector produces a uniformly distributed point of the sphere. This identity is the basic bridge between averages over the orthogonal group and averages over the sphere; it is the tool behind the uniqueness of rotation-invariant laws on the sphere and behind the computation of averages over block rotations.
--
--   **Formalization Note** `Orthogonal E` is `unitary (E →L[ℝ] E)`, `orthogonalLaw` is `Measure.haarMeasure` normalized to give the whole compact group mass $1$, and `act u x` is $Ux$. `SubsphereRegression.ambientSphereLaw` is the image under the inclusion of the unit sphere into $E$ of the normalized measure `(volume.toSphere univ)⁻¹ • volume.toSphere` induced by Lebesgue measure. The integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions; nontriviality of $E$ is the instance `[Nontrivial E]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Mixture/Haar.lean#L55-L71

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

theorem OAI.SubsphereCurrent.Mixture.haar_eval_integral [Nontrivial E] {x : E} (hx : ‖x‖ = 1)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ u, f (act u x) ∂orthogonalLaw) = ∫⁻ y, f y ∂SubsphereRegression.ambientSphereLaw := by sorry
