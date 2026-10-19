-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Mixture_latitudeLaw_beta_gt_one
-- name    : OAI.SubsphereCurrent.Mixture.latitudeLaw_beta_gt_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:20:54.322849+00:00
-- url     : https://prove2.me/theorems/4b2cc83d-19bd-4c59-9f80-f67c4d792c79
-- title:
--   Perpendicular coordinate of a latitude law for $\dim V>1$: $\mathrm{Beta}(a,\ \delta+(\dim V-1)/2)$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, equipped with its Borel $\sigma$-algebra. For a finite-dimensional real inner product space $K$ (for instance $E$ or one of its subspaces) write $O(K)$ for its orthogonal group, the compact group of linear isometries of $K$, and $H_K$ for the Haar probability measure on $O(K)$; write $\sigma_K$ for the uniform (normalized rotation-invariant surface) probability measure on the unit sphere $\{y\in K:\|y\|=1\}$, regarded as a measure on $K$. For a subspace $V\subseteq E$ let $P_V$ and $P_{V^\perp}$ be the orthogonal projections onto $V$ and onto its orthogonal complement $V^\perp$.
--
--   Fix a linear subspace $V\subseteq E$ and a unit vector $e\in V$, and let $L=e^\perp=\{y\in E:\langle y,e\rangle=0\}$ be the hyperplane of $E$ orthogonal to $e$. For $u\in O(V)$ and $w\in O(V^\perp)$ let $B_{u,w}$ be the block-diagonal isometry of $E$ that acts by $u$ on $V$ and by $w$ on $V^\perp$:
--   $$
--   B_{u,w}(y)=u(P_Vy)+w(P_{V^\perp}y)\qquad(y\in E).
--   $$
--   For real $a,\delta$ the latitude law $\mathcal L^{a,\delta}_{V,e}$ is the law of
--   $$
--   B_{U,1}\bigl(\sqrt{1-Q}\,e+\sqrt{Q}\,Z\bigr),\qquad Q\sim\mathrm{Beta}(a,\delta),\quad U\sim H_V,\quad Z\sim\sigma_L\ \text{independent},
--   $$
--   that is, the image of $\mathrm{Beta}(a,\delta)\otimes H_V\otimes\sigma_L$ under $(q,U,z)\mapsto B_{U,1}(\sqrt{1-q}\,e+\sqrt q\,z)$: a beta-distributed height $Q$ mixes $e$ with a uniform unit vector orthogonal to $e$, and the result is turned by a Haar-random orthogonal map of $V$ (acting trivially on $V^\perp$).
--
--   Here $\mathrm{Beta}(\alpha,\beta)$ denotes the measure on $\mathbb{R}$ with density $q^{\alpha-1}(1-q)^{\beta-1}/B(\alpha,\beta)$ on $(0,1)$ (and $0$ elsewhere) with respect to Lebesgue measure, where $B(\alpha,\beta)=\Gamma(\alpha)\Gamma(\beta)/\Gamma(\alpha+\beta)$; for positive parameters it is the beta probability distribution.
--
--   Assume $1<\dim V<\dim E$, and let $a>0$ and $\delta>0$ satisfy $a+\delta=\frac{\dim E-\dim V}{2}$. Then the perpendicular coordinate $x\mapsto\|P_{V^\perp}x\|^2$ is measure preserving from $\mathcal L^{a,\delta}_{V,e}$ to a beta law:
--   $$
--   \mathcal L^{a,\delta}_{V,e}\bigl(\{x\in E:\ \|P_{V^\perp}x\|^2\in A\}\bigr)=\mathrm{Beta}\Bigl(a,\ \delta+\frac{\dim V-1}{2}\Bigr)(A)\qquad\text{for every Borel set }A\subseteq\mathbb{R}.
--   $$
--
--   Together with the block invariance of latitude laws, this exact scalar law is what makes latitude laws usable as explicit comparison measures: the perpendicular coordinate of a latitude law is again beta distributed, with the first parameter $a$ unchanged and the second parameter enlarged by $(\dim V-1)/2$.
--
--   **Formalization Note** `Orthogonal K` is `unitary (K →L[ℝ] K)`, `orthogonalLaw` is `Measure.haarMeasure` normalized to give the whole compact group mass $1$, and `SubsphereRegression.ambientSphereLaw` is the image under the inclusion of the unit sphere into the space of the normalized measure `(volume.toSphere univ)⁻¹ • volume.toSphere` induced by Lebesgue measure. `blockIso V u w` is $B_{u,w}$, built from the orthogonal decomposition of $E$ into $V$ and $V^\perp$. `MeasurePreserving T μ ν` means that $T$ is measurable and the image of $\mu$ under $T$ equals $\nu$. `latitudeSpace V e` is the orthogonal complement of the span of $e$ in $E$, `latitudeLaw V e a delta` is the image measure described above, `perpCoordinate V x` is $\|P_{V^\perp}x\|^2$, and the beta law is Mathlib's `betaMeasure`. Dimensions are `Module.finrank`, cast to real numbers before subtracting.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Mixture/Latitude.lean#L268-L313

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

theorem OAI.SubsphereCurrent.Mixture.latitudeLaw_beta_gt_one (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (hV : 1 < Module.finrank ℝ V) (hD : Module.finrank ℝ V < Module.finrank ℝ E)
    {a delta : ℝ} (ha : 0 < a) (hd : 0 < delta)
    (hshape : a+delta = ((Module.finrank ℝ E : ℝ)-(Module.finrank ℝ V : ℝ))/2) :
    MeasurePreserving (perpCoordinate V) (latitudeLaw V e a delta)
      (betaMeasure a (delta+((Module.finrank ℝ V : ℝ)-1)/2)) := by sorry
