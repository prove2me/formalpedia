-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Slice_ballCap_integral
-- name    : OAI.SubsphereCurrent.Slice.ballCap_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:52:33.023991+00:00
-- url     : https://prove2.me/theorems/d1468895-bb7f-4cc8-8bbc-2392f5d02e12
-- title:
--   Volume integral of a capped radial extension of a section-controlled function
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra. Every subspace $W$ of $E$ is itself an inner product space and carries its Lebesgue measure $\mathrm{vol}_W$ (the Haar measure giving an orthonormal cube volume $1$); write $S(W)$ for its unit sphere, $B_W=\{w\in W:\lVert w\rVert<1\}$ for its open unit ball, $\sigma_W(Y)=\dim W\cdot\mathrm{vol}_W(\{\rho y:\ y\in Y,\ 0<\rho<1\})$ for its surface measure, and $\bar\sigma_W=\sigma_W(S(W))^{-1}\sigma_W$ for the normalized surface measure.
--
--   Let $g:S(E)\to[0,\infty]$, $k,b\in\mathbb{N}$ and $C\in[0,\infty]$. Say that $g$ is *$(k,b,C)$-controlled* if for every $k$-dimensional subspace $W\subseteq E$, every $c\in W^{\perp}$ and every $\rho>0$ with $\lVert c\rVert^2+\rho^2=1$,
--   $$
--   \rho^{\,b}\int_{S(W)}g(c+\rho w)\,d\bar\sigma_W(w)\le C .
--   $$
--   For $z\in E$ and $t\in\mathbb{R}$, the *capped radial extension* $h_{z,t}:E\to[0,\infty]$ is $h_{z,t}(y)=g(y/\lVert y\rVert)$ if $0<\lVert y\rVert<1$ and $\lVert y/\lVert y\rVert-z\rVert\le t$, and $h_{z,t}(y)=0$ otherwise.
--
--   **Theorem.** Suppose that $g$ is measurable and $(k,b,C)$-controlled, that $K\subseteq E$ is a nonzero subspace with $\dim K=k$ and $b+1\le k$, that $z\in K^{\perp}$, and that $t>0$. Then
--   $$
--   \int_E h_{z,t}\,d\,\mathrm{vol}_E\ \le\ \sigma_K\bigl(S(K)\bigr)\cdot C\cdot\frac{t^{\,k-b}}{k-b}\cdot\mathrm{vol}_{K^{\perp}}\bigl(B_{K^{\perp}}\bigr).
--   $$
--
--   The control hypothesis bounds weighted averages of $g$ over all $k$-dimensional affine sections of the sphere. The theorem converts it into a bound for the volume integral of the part of the radial extension of $g$ whose direction lies in the cap $\{s:\lVert s-z\rVert\le t\}$; the factor $t^{k-b}$ reflects that the cap is thin in the $k$ directions of $K$. It is the main input for bounding the spherical average of $g$ over such a cap.
--
--   **Formalization Note** The control condition is `Slice.Controlled g k b C`, quantifying over the slice tests `Slice.Test E k`; $h_{z,t}$ is `ballCap g z t`, the indicator of the open unit ball times `Polar.radial (capFunction g z t)`, and $\sigma_W$ is Mathlib's `Measure.toSphere` of `volume`. The hypothesis that $K$ is nonzero is the instance `[Nontrivial K]` (it also follows from $\dim K=k\ge1$); the factor $t^{k-b}/(k-b)$ enters through `ENNReal.ofReal`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Geometry/Integration.lean#L619-L680

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

omit [Nontrivial E] in
theorem OAI.SubsphereCurrent.Slice.ballCap_integral {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g)
    {k b : ℕ} {C : ℝ≥0∞} (hc : Controlled g k b C)
    (K : Submodule ℝ E) [Nontrivial K] (hK : Module.finrank ℝ K = k)
    (hb : b+1 ≤ k) {z : E} (hz : z ∈ Kᗮ) {t : ℝ} (ht : 0 < t) :
    (∫⁻ y : E, ballCap g z t y ∂volume) ≤
      ((volume : Measure K).toSphere univ) * C *
        ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ)) *
          (volume : Measure Kᗮ) (Metric.ball 0 1) := by sorry
