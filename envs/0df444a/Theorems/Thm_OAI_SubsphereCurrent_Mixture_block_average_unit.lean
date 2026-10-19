-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Mixture_block_average_unit
-- name    : OAI.SubsphereCurrent.Mixture.block_average_unit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:12:29.417583+00:00
-- url     : https://prove2.me/theorems/ec435c4e-0cc3-43a6-95de-bf8671f23c41
-- title:
--   Block-orthogonal averages of a unit vector as a mixture of two independent sphere laws
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, equipped with its Borel $\sigma$-algebra. For a finite-dimensional real inner product space $K$ (for instance $E$ or one of its subspaces) write $O(K)$ for its orthogonal group, the compact group of linear isometries of $K$, and $H_K$ for the Haar probability measure on $O(K)$; write $\sigma_K$ for the uniform (normalized rotation-invariant surface) probability measure on the unit sphere $\{y\in K:\|y\|=1\}$, regarded as a measure on $K$. For a subspace $V\subseteq E$ let $P_V$ and $P_{V^\perp}$ be the orthogonal projections onto $V$ and onto its orthogonal complement $V^\perp$.
--
--   Fix a subspace $V\subseteq E$ such that both $V$ and $V^\perp$ are nonzero. For $u\in O(V)$ and $w\in O(V^\perp)$ let $B_{u,w}$ be the block-diagonal isometry of $E$ that acts by $u$ on $V$ and by $w$ on $V^\perp$:
--   $$
--   B_{u,w}(y)=u(P_Vy)+w(P_{V^\perp}y)\qquad(y\in E).
--   $$
--
--   Let $x\in E$ be a unit vector and put $t=\|P_{V^\perp}x\|^2\in[0,1]$. Then for every measurable function $f:E\to[0,\infty]$,
--   $$
--   \int_{O(V)\times O(V^\perp)} f\bigl(B_{u,w}x\bigr)\,d\bigl(H_V\otimes H_{V^\perp}\bigr)(u,w)
--   =\int_{V\times V^\perp} f\bigl(\sqrt{1-t}\,s+\sqrt{t}\,r\bigr)\,d\bigl(\sigma_V\otimes\sigma_{V^\perp}\bigr)(s,r).
--   $$
--
--   Probabilistically: if $u$ and $w$ are independent Haar-random orthogonal maps of $V$ and of $V^\perp$, then $B_{u,w}x$ has the same law as $\sqrt{1-t}\,S+\sqrt t\,R$, where $S$ and $R$ are independent and uniform on the unit spheres of $V$ and of $V^\perp$. So the law of a unit vector under the block rotation group depends on the vector only through the scalar $t$; this common kernel is how block-invariant laws on the sphere (direction and latitude laws) are compared with one another.
--
--   **Formalization Note** `Orthogonal K` is `unitary (K →L[ℝ] K)`, `orthogonalLaw` is `Measure.haarMeasure` normalized to give the whole compact group mass $1$, and `SubsphereRegression.ambientSphereLaw` is the image under the inclusion of the unit sphere into the space of the normalized measure `(volume.toSphere univ)⁻¹ • volume.toSphere` induced by Lebesgue measure. `blockIso V u w` is $B_{u,w}$, built from the orthogonal decomposition of $E$ into $V$ and $V^\perp$. `MeasurePreserving T μ ν` means that $T$ is measurable and the image of $\mu$ under $T$ equals $\nu$. The map $(t,(s,r))\mapsto\sqrt{1-t}\,s+\sqrt t\,r$ is `mixtureSampler V`, and $t$ is `perpCoordinate V x`, defined as $\|P_{V^\perp}x\|^2$. Nonzeroness of $V$ and $V^\perp$ is expressed by the instances `[Nontrivial V] [Nontrivial Vᗮ]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Mixture/BetaTheory.lean#L133-L151

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
  [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereCurrent.Mixture.block_average_unit (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ]
    {x : E} (hx : ‖x‖ = 1) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : Orthogonal V × Orthogonal Vᗮ, f (blockIso V z.1 z.2 x)
      ∂(orthogonalLaw (E := V)).prod (orthogonalLaw (E := Vᗮ))) =
    ∫⁻ z : V × Vᗮ, f (mixtureSampler V (perpCoordinate V x,z))
      ∂(SubsphereRegression.ambientSphereLaw (E := V)).prod
        (SubsphereRegression.ambientSphereLaw (E := Vᗮ)) := by sorry
