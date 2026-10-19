-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Mixture_directionLaw_beta
-- name    : OAI.SubsphereCurrent.Mixture.directionLaw_beta
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:16:23.512125+00:00
-- url     : https://prove2.me/theorems/89c6b96b-7cc4-4228-913b-ace4ccdba430
-- title:
--   The perpendicular coordinate of the direction law is $\mathrm{Beta}((\dim N-\dim V)/2,\ \dim V/2)$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, equipped with its Borel $\sigma$-algebra. For a finite-dimensional real inner product space $K$ (for instance $E$ or one of its subspaces) write $O(K)$ for its orthogonal group, the compact group of linear isometries of $K$, and $H_K$ for the Haar probability measure on $O(K)$; write $\sigma_K$ for the uniform (normalized rotation-invariant surface) probability measure on the unit sphere $\{y\in K:\|y\|=1\}$, regarded as a measure on $K$. For a subspace $V\subseteq E$ let $P_V$ and $P_{V^\perp}$ be the orthogonal projections onto $V$ and onto its orthogonal complement $V^\perp$.
--
--   Fix linear subspaces $V,N\subseteq E$. For $u\in O(V)$ and $w\in O(V^\perp)$ let $B_{u,w}$ be the block-diagonal isometry of $E$ that acts by $u$ on $V$ and by $w$ on $V^\perp$:
--   $$
--   B_{u,w}(y)=u(P_Vy)+w(P_{V^\perp}y)\qquad(y\in E).
--   $$
--   The direction law $\mathcal D_{V,N}$ is the law of $B_{1,W}(Y)$, where $W\sim H_{V^\perp}$ and $Y\sim\sigma_N$ are independent: a uniform unit vector of $N$ whose $V^\perp$-component is then turned by an independent Haar-random orthogonal map of $V^\perp$, while its $V$-component is left unchanged.
--
--   Assume $V\subseteq N$ and $0<\dim V<\dim N$. Then the perpendicular coordinate $x\mapsto\|P_{V^\perp}x\|^2$ is measure preserving from $\mathcal D_{V,N}$ to a beta law:
--   $$
--   \mathcal D_{V,N}\bigl(\{x\in E:\ \|P_{V^\perp}x\|^2\in A\}\bigr)=\mathrm{Beta}\Bigl(\frac{\dim N-\dim V}{2},\ \frac{\dim V}{2}\Bigr)(A)\qquad\text{for every Borel set }A\subseteq\mathbb{R}.
--   $$
--   Here $\mathrm{Beta}(\alpha,\beta)$ denotes the measure on $\mathbb{R}$ with density $q^{\alpha-1}(1-q)^{\beta-1}/B(\alpha,\beta)$ on $(0,1)$ (and $0$ elsewhere) with respect to Lebesgue measure, where $B(\alpha,\beta)=\Gamma(\alpha)\Gamma(\beta)/\Gamma(\alpha+\beta)$; for positive parameters it is the beta probability distribution.
--
--   Because $\mathcal D_{V,N}$ is invariant under all block maps $B_{u,w}$ (a companion lemma), the scalar coordinate $\|P_{V^\perp}x\|^2$ is the natural statistic through which it is compared with the uniform sphere law and with latitude laws; this lemma identifies the law of that coordinate exactly.
--
--   **Formalization Note** `Orthogonal K` is `unitary (K →L[ℝ] K)`, `orthogonalLaw` is `Measure.haarMeasure` normalized to give the whole compact group mass $1$, and `SubsphereRegression.ambientSphereLaw` is the image under the inclusion of the unit sphere into the space of the normalized measure `(volume.toSphere univ)⁻¹ • volume.toSphere` induced by Lebesgue measure. `blockIso V u w` is $B_{u,w}$, built from the orthogonal decomposition of $E$ into $V$ and $V^\perp$. `MeasurePreserving T μ ν` means that $T$ is measurable and the image of $\mu$ under $T$ equals $\nu$. `directionLaw V N` is the image of `orthogonalLaw (E := Vᗮ)` times `ambientSphereLaw (E := N)` under $(W,Y)\mapsto B_{1,W}Y$; `perpCoordinate V x` is $\|P_{V^\perp}x\|^2$; the beta law is Mathlib's `betaMeasure`. The dimensions are `Module.finrank`, cast to real numbers before subtracting, so $\dim N-\dim V$ is an ordinary difference.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Mixture/Latitude.lean#L106-L122

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

theorem OAI.SubsphereCurrent.Mixture.directionLaw_beta (V N : Submodule ℝ E) (hVN : V ≤ N)
    (hV : 0 < Module.finrank ℝ V) (hN : Module.finrank ℝ V < Module.finrank ℝ N) :
    MeasurePreserving (perpCoordinate V) (directionLaw V N)
      (betaMeasure (((Module.finrank ℝ N : ℝ)-(Module.finrank ℝ V : ℝ))/2)
        ((Module.finrank ℝ V : ℝ)/2)) := by sorry
