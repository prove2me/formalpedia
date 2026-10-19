-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Mixture_directionLaw_domination
-- name    : OAI.SubsphereCurrent.Mixture.directionLaw_domination
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:24:11.085835+00:00
-- url     : https://prove2.me/theorems/ff6ce2ef-d347-4b41-88f3-5d588b02c4f1
-- title:
--   A randomly rotated uniform direction of a subspace is dominated by $2^{\dim E}$ times the uniform sphere law plus a latitude law
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, and put $D=\dim E$. For a linear subspace $W\subseteq E$ (including $W=E$) write $\sigma_W$ for the uniform probability measure on the unit sphere $S(W)=\{x\in W:\|x\|=1\}$ (normalized surface measure), regarded as a measure on $E$, and write $\mathrm{O}(W)$ for the orthogonal group of $W$, equipped with its Haar probability measure. For a subspace $V$ with orthogonal complement $V^\perp$ and orthogonal projections $P_V,P_{V^\perp}$, every pair $u\in\mathrm{O}(V)$, $w\in\mathrm{O}(V^\perp)$ defines the block isometry
--
--   $$
--   R_{u,w}(x)=u(P_Vx)+w(P_{V^\perp}x),\qquad x\in E .
--   $$
--
--   For $\alpha,\beta>0$, $\mathrm{Beta}(\alpha,\beta)$ denotes the probability measure on $\mathbb{R}$ with density $x^{\alpha-1}(1-x)^{\beta-1}/B(\alpha,\beta)$ on $(0,1)$, where $B$ is the Beta function.
--
--   Fix subspaces $V\subseteq N\subseteq E$ whose dimensions $j=\dim V$ and $n=\dim N$ satisfy $1\le j<n<D$, and fix a unit vector $e\in V$. Two probability laws on $E$ are built from these data.
--
--   1. The **direction law** $\mu_{V,N}$ is the law of $R_{1,G}(X)$, where $X\sim\sigma_N$ and a Haar-random $G\in\mathrm{O}(V^\perp)$ are independent. Thus a uniform unit vector of $N$ keeps its component in $V$, while its component orthogonal to $V$ is rotated by an independent uniformly random orthogonal map of $V^\perp$.
--   2. For $a,\delta>0$ the **latitude law** $\lambda^{a,\delta}_{V,e}$ is the law of $R_{U,1}\big(\sqrt{1-Q}\,e+\sqrt{Q}\,Y\big)$, where $Q\sim\mathrm{Beta}(a,\delta)$, a Haar-random $U\in\mathrm{O}(V)$ and $Y\sim\sigma_{e^\perp}$ are independent, and $e^\perp=\{x\in E:\langle x,e\rangle=0\}$. Thus a unit vector at latitude $\sqrt{1-Q}$ with respect to the pole $e$ and with a uniform direction in $e^\perp$ is moved by a uniformly random orthogonal map of $V$ (fixing $V^\perp$ pointwise).
--
--   **Theorem.** With $a=\frac{n-j}{2}$ and $\delta=\frac{D-n}{2}$, for every Borel set $H\subseteq E$,
--
--   $$
--   \mu_{V,N}(H)\;\le\;2^{D}\Big(\sigma_E(H)+\lambda^{\frac{n-j}{2},\,\frac{D-n}{2}}_{V,e}(H)\Big),
--   $$
--
--   that is, $\mu_{V,N}\le 2^{\dim E}\big(\sigma_E+\lambda^{a,\delta}_{V,e}\big)$ as measures on $E$.
--
--   The direction law describes a uniform direction of an intermediate subspace that has been randomized only orthogonally to $V$. The theorem bounds it, at the cost of the factor $2^{\dim E}$, by the sum of two explicit laws that are invariant under every block isometry $R_{u,w}$: the uniform law on the whole sphere and a latitude law attached to the pole $e$. It is the first of the three assertions of the mixture estimate in the main theorem of this development, and it allows probabilities and integrals under $\mu_{V,N}$ to be bounded by the corresponding quantities for these two reference laws.
--
--   **Formalization Note** Measures take values in $[0,\infty]$, and the inequality is the order on measures, which compares the masses of all (equivalently, of all measurable) sets. The orthogonal group of a subspace $W$ is the group of unitary elements of the algebra of continuous linear maps $W\to W$, with Haar measure normalized to total mass $1$ (`orthogonalLaw`); the uniform sphere law is the normalized `toSphere` measure of Lebesgue measure, pushed forward into the ambient space (`SubsphereRegression.ambientSphereLaw`). The parameters $\frac{n-j}{2}$ and $\frac{D-n}{2}$ are real numbers computed from the natural-number dimensions; `latitudeLaw V e a delta` itself accepts arbitrary real parameters, and $e$ is given as a point of the unit sphere of the subspace $V$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Mixture/Domination.lean#L207-L282

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
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Domination

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Mixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereCurrent.Mixture.directionLaw_domination (V N : Submodule ℝ E) (hVN : V ≤ N)
    (hj : 1 ≤ Module.finrank ℝ V) (hjn : Module.finrank ℝ V < Module.finrank ℝ N)
    (hnD : Module.finrank ℝ N < Module.finrank ℝ E) (e : Metric.sphere (0 : V) 1) :
    directionLaw V N ≤ (2 : ℝ≥0∞)^Module.finrank ℝ E •
      (SubsphereRegression.ambientSphereLaw + latitudeLaw V e
        (((Module.finrank ℝ N : ℝ)-(Module.finrank ℝ V : ℝ))/2)
        (((Module.finrank ℝ E : ℝ)-(Module.finrank ℝ N : ℝ))/2)) := by sorry
