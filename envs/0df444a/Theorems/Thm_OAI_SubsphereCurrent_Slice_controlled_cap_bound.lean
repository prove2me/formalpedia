-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Slice_controlled_cap_bound
-- name    : OAI.SubsphereCurrent.Slice.controlled_cap_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:53:16.741694+00:00
-- url     : https://prove2.me/theorems/f6667b4e-8c05-4ed7-97e3-09a6b3763ecc
-- title:
--   Spherical caps carry little mass under section-controlled functions
-- statement:
--   Let $E\neq0$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra. For a nonzero subspace $W\subseteq E$ (in particular $W=E$) write $S(W)$ for its unit sphere and $\bar\sigma_W$ for the normalized surface measure, i.e. the uniform probability measure on $S(W)$.
--
--   Let $g:S(E)\to[0,\infty]$, $k,b\in\mathbb{N}$ and $C\in[0,\infty]$. Say that $g$ is *$(k,b,C)$-controlled* if for every $k$-dimensional subspace $W\subseteq E$, every $c\in W^{\perp}$ and every $\rho>0$ with $\lVert c\rVert^2+\rho^2=1$,
--   $$
--   \rho^{\,b}\int_{S(W)}g(c+\rho w)\,d\bar\sigma_W(w)\le C,
--   $$
--   that is, the averages of $g$ over the $k$-dimensional affine sections $\{c+\rho w:\ w\in S(W)\}$ of the sphere, weighted by $\rho^b$, are at most $C$.
--
--   **Theorem.** Suppose that $g$ is measurable and $(k,b,C)$-controlled, that $K\subseteq E$ is a nonzero subspace with $\dim K=k$, $b+1\le k$ and $2b\le k$, that $z\in K^{\perp}$, and that $t>0$. Then
--   $$
--   \int_{S(E)}g(s)\,\mathbf{1}\bigl\{\lVert s-z\rVert\le t\bigr\}\,d\bar\sigma_E(s)\ \le\ 2^{\dim E+1}\,C\,t^{\,k-b}.
--   $$
--
--   So a function whose weighted $k$-dimensional section averages are controlled puts mass at most $2^{\dim E+1}C\,t^{k-b}$ on the cap of Euclidean radius $t$ around a point $z$ orthogonal to a $k$-dimensional subspace. The exponent $k-b$ is the gain from the $k$ directions in which the cap is thin, minus the loss $b$ allowed by the radius weight. This is the form in which section control is turned into a bound on the probability of landing close to a target point.
--
--   **Formalization Note** The control condition is `Slice.Controlled g k b C`, the integrand is `capFunction g z t` and $\bar\sigma_E$ is `Affine.sphereLaw E`; $E\neq0$ and $K\neq0$ are the instances `[Nontrivial E]` and `[Nontrivial K]`, and $t^{k-b}$ enters through `ENNReal.ofReal`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Geometry/Integration.lean#L705-L738

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

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Slice
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem OAI.SubsphereCurrent.Slice.controlled_cap_bound {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g)
    {k b : ℕ} {C : ℝ≥0∞} (hc : Controlled g k b C)
    (K : Submodule ℝ E) [Nontrivial K] (hK : Module.finrank ℝ K = k)
    (hb : b+1 ≤ k) (h2b : 2*b ≤ k) {z : E} (hz : z ∈ Kᗮ) {t : ℝ} (ht : 0 < t) :
    (∫⁻ s, capFunction g z t s ∂Affine.sphereLaw E) ≤
      (2 : ℝ≥0∞)^(Module.finrank ℝ E+1) * C * ENNReal.ofReal (t^(k-b)) := by sorry
