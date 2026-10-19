-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_ambientSphereLaw_closedBall
-- name    : OAI.SubsphereRegression.ambientSphereLaw_closedBall
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:23:28.790693+00:00
-- url     : https://prove2.me/theorems/14c8bc24-b113-4b00-8fbd-fffbdc478286
-- title:
--   Polynomial ball-mass bound for the uniform measure on the unit sphere
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $d\ge1$ with its Borel $\sigma$-algebra and its Lebesgue measure $\lambda_E$ (the Haar measure giving the cube spanned by an orthonormal basis volume $1$). Let $S=\{x\in E:\|x\|=1\}$ be the unit sphere, and let $\sigma_E$ be the normalized surface measure on $S$: the surface measure induced by $\lambda_E$, for which a measurable $s\subseteq S$ has measure $d\cdot\lambda_E\bigl((0,1)\cdot s\bigr)$, divided by its total mass, so that $\sigma_E$ is a probability measure. Here $(0,1)\cdot s=\{cx:0<c<1,\ x\in s\}$. Write $\tilde\sigma_E$ for the image of $\sigma_E$ under the inclusion $S\hookrightarrow E$, that is, the uniform probability measure on the unit sphere regarded as a Borel measure on $E$, and $\bar B(z,r)=\{x\in E:\|x-z\|\le r\}$ for closed balls.
--
--   Then for every centre $z\in E$, every radius $r>0$ and every integer $k$ with $0\le k\le d-1$,
--   $$\tilde\sigma_E\bigl(\bar B(z,r)\bigr)\;\le\;3\cdot4^{d}\,r^{k}.$$
--
--   Unlike the cap estimate, this holds for all radii $r>0$ and arbitrary centres, at the cost of allowing any exponent $k\le d-1$ instead of exactly $d-1$. In other words, $\tilde\sigma_E$ satisfies the polynomial mass condition $\tilde\sigma_E(\bar B(z,r))\le C\,r^{k}$ for all centres and radii, with $C=3\cdot4^{d}$ and any order $k\le d-1$; this is the kind of regularity that mass and moment bounds for spread-out priors on an unknown vector require.
--
--   **Formalization Note** $\tilde\sigma_E$ is `ambientSphereLaw`, the pushforward of `sphereLaw` along the coercion from the sphere subtype to $E$; $E$ is assumed nontrivial, so $d\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Spheres.lean#L137-L156

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.ambientSphereLaw_closedBall [Nontrivial E] (z : E) {r : ℝ} (hr : 0 < r)
    (k : ℕ) (hk : k ≤ Module.finrank ℝ E - 1) :
    ambientSphereLaw (Metric.closedBall z r) ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) * ENNReal.ofReal (r^k) := by sorry
