-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_sphere_three_orbit_bound
-- name    : OAI.SubsphereRegression.sphere_three_orbit_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:02:41.665912+00:00
-- url     : https://prove2.me/theorems/2050b9a4-060d-4af4-bf0c-6a34d9daef71
-- title:
--   Sphere sets determined up to $1/5$ by a small projection have measure at most $7/16$
-- statement:
--   Let $E$ be a nontrivial finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $S_E$ be its unit sphere and $\sigma_E$ the uniform (normalized surface) probability measure on $S_E$. Let $F\subseteq E$ be a linear subspace whose orthogonal complement is small, $16\dim F^\perp\le\dim E$, and suppose $F$ carries a *quarter turn*: a linear isometry $e:F\to F$ with $\langle x,e(x)\rangle=0$ and $e(e(x))=-x$ for all $x\in F$. Let $S\subseteq S_E$ be a $\sigma_E$-null-measurable set and assume that any two points of $S$ that cannot be distinguished by inner products with vectors of $F^\perp$ are close: for all $x,y\in S_E$,
--   $$\Big(\langle u,x\rangle=\langle u,y\rangle\ \text{for all }u\in F^\perp\Big)\ \text{and}\ x\in S\ \text{and}\ y\in S\ \Longrightarrow\ \|x-y\|\le\tfrac15 .$$
--
--   **Theorem.** Under these hypotheses,
--
--   $$
--   \sigma_E(S)\le\frac{7}{16}.
--   $$
--
--   Think of $F^\perp$ as containing the measurement directions available to an estimator: a set of directions that is determined, up to error $1/5$, by its projection onto a subspace of dimension at most $\dim E/16$ has uniform measure below one half. This is the geometric core of the statement that a learner seeing at most $d/32$ Gaussian rows cannot estimate a uniformly random unit vector to angular accuracy $1/10$ with probability more than $7/16$.
--
--   **Formalization Note** The measure is `SubsphereRegression.sphereLaw`, the normalized `volume.toSphere` on `Metric.sphere (0 : E) 1`; the closeness hypothesis is stated for all pairs of unit vectors, and $e$ is a `LinearIsometryEquiv` of $F$ onto itself.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Estimates/HalfPrecision.lean#L63-L123

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

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.sphere_three_orbit_bound [Nontrivial E] (F : Submodule ℝ E)
    (hF : 16*Module.finrank ℝ Fᗮ ≤ Module.finrank ℝ E)
    (e : F ≃ₗᵢ[ℝ] F) (he : ∀ x, ⟪x,e x⟫ = 0) (he2 : ∀ x, e (e x) = -x)
    (S : Set (Metric.sphere (0 : E) 1)) (hS : NullMeasurableSet S sphereLaw)
    (hnear : ∀ x y : Metric.sphere (0 : E) 1,
      (∀ u : E, u ∈ Fᗮ → ⟪u,x.val⟫ = ⟪u,y.val⟫) → x ∈ S → y ∈ S →
      dist x.val y.val ≤ 1/5) :
    sphereLaw S ≤ ENNReal.ofReal (7/16 : ℝ) := by sorry
