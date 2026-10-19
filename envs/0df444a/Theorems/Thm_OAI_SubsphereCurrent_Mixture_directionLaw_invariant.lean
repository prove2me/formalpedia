-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Mixture_directionLaw_invariant
-- name    : OAI.SubsphereCurrent.Mixture.directionLaw_invariant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:15:06.652361+00:00
-- url     : https://prove2.me/theorems/64ac660c-4613-467b-81eb-92a604e23c0d
-- title:
--   Direction laws are invariant under block-diagonal orthogonal maps
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, equipped with its Borel $\sigma$-algebra. For a finite-dimensional real inner product space $K$ (for instance $E$ or one of its subspaces) write $O(K)$ for its orthogonal group, the compact group of linear isometries of $K$, and $H_K$ for the Haar probability measure on $O(K)$; write $\sigma_K$ for the uniform (normalized rotation-invariant surface) probability measure on the unit sphere $\{y\in K:\|y\|=1\}$, regarded as a measure on $K$. For a subspace $V\subseteq E$ let $P_V$ and $P_{V^\perp}$ be the orthogonal projections onto $V$ and onto its orthogonal complement $V^\perp$.
--
--   Fix linear subspaces $V,N\subseteq E$. For $u\in O(V)$ and $w\in O(V^\perp)$ let $B_{u,w}$ be the block-diagonal isometry of $E$ that acts by $u$ on $V$ and by $w$ on $V^\perp$:
--   $$
--   B_{u,w}(y)=u(P_Vy)+w(P_{V^\perp}y)\qquad(y\in E).
--   $$
--   The direction law $\mathcal D_{V,N}$ is the law of $B_{1,W}(Y)$, where $W\sim H_{V^\perp}$ and $Y\sim\sigma_N$ are independent: a uniform unit vector of $N$ whose $V^\perp$-component is then turned by an independent Haar-random orthogonal map of $V^\perp$, while its $V$-component is left unchanged.
--
--   Assume that $N\neq\{0\}$ and $V\subseteq N$. Then for every $u\in O(V)$ and every $w\in O(V^\perp)$ the isometry $B_{u,w}$ preserves the direction law:
--   $$
--   \bigl(B_{u,w}\bigr)_{*}\,\mathcal D_{V,N}=\mathcal D_{V,N}.
--   $$
--
--   The direction law thus has the full symmetry of the block group $O(V)\times O(V^\perp)$, although only the $V^\perp$-part is randomized explicitly. This symmetry is what allows $\mathcal D_{V,N}$ to be compared with other block-invariant laws on the sphere through the single scalar coordinate $\|P_{V^\perp}x\|^2$.
--
--   **Formalization Note** `Orthogonal K` is `unitary (K →L[ℝ] K)`, `orthogonalLaw` is `Measure.haarMeasure` normalized to give the whole compact group mass $1$, and `SubsphereRegression.ambientSphereLaw` is the image under the inclusion of the unit sphere into the space of the normalized measure `(volume.toSphere univ)⁻¹ • volume.toSphere` induced by Lebesgue measure. `blockIso V u w` is $B_{u,w}$, built from the orthogonal decomposition of $E$ into $V$ and $V^\perp$. `MeasurePreserving T μ ν` means that $T$ is measurable and the image of $\mu$ under $T$ equals $\nu$. `directionLaw V N` is the image of `orthogonalLaw (E := Vᗮ)` times `ambientSphereLaw (E := N)` under $(W,Y)\mapsto B_{1,W}Y$. The hypothesis $N\neq\{0\}$ is the instance `[Nontrivial N]`; no condition on $V$ other than $V\subseteq N$ is imposed (in particular $V=\{0\}$ is allowed).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Mixture/Latitude.lean#L91-L104

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
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Latitude

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Mixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereCurrent.Mixture.directionLaw_invariant (V N : Submodule ℝ E) [Nontrivial N] (hVN : V ≤ N)
    (u : Orthogonal V) (w : Orthogonal Vᗮ) :
    MeasurePreserving (blockIso V u w) (directionLaw V N) (directionLaw V N) := by sorry
