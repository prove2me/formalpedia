-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_terminal_cap_mass
-- name    : OAI.SubsphereRegression.terminal_cap_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:23:58.2677+00:00
-- url     : https://prove2.me/theorems/3830dd57-ec14-410f-a15f-5475966f2b18
-- title:
--   Uniform sphere measure of the intersection of two balls
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $d\ge1$ with its Borel $\sigma$-algebra and its Lebesgue measure $\lambda_E$ (the Haar measure giving the cube spanned by an orthonormal basis volume $1$). Let $S=\{x\in E:\|x\|=1\}$ be the unit sphere, and let $\sigma_E$ be the normalized surface measure on $S$: the surface measure induced by $\lambda_E$, for which a measurable $s\subseteq S$ has measure $d\cdot\lambda_E\bigl((0,1)\cdot s\bigr)$, divided by its total mass, so that $\sigma_E$ is a probability measure. Here $(0,1)\cdot s=\{cx:0<c<1,\ x\in s\}$. Write $\tilde\sigma_E$ for the image of $\sigma_E$ under the inclusion $S\hookrightarrow E$, that is, the uniform probability measure on the unit sphere regarded as a Borel measure on $E$, and $\bar B(z,r)=\{x\in E:\|x-z\|\le r\}$ for closed balls.
--
--   Let $y,z\in E$, let $\varepsilon>0$ and $r>0$, and let $a\ge0$ be an integer with $2a\le d-1$. Then
--   $$\tilde\sigma_E\bigl(\bar B(y,\varepsilon)\cap\bar B(z,r)\bigr)\;\le\;3\cdot4^{d}\,\varepsilon^{a}\,r^{a}.$$
--
--   The bound splits the available smallness evenly between the two radii, so it is small as soon as either ball is small. This is the form needed when one radius is an accuracy parameter and the other a localization radius, and both should appear in the estimate.
--
--   **Formalization Note** The left-hand side is written as the restriction of `ambientSphereLaw` to $\bar B(y,\varepsilon)$ evaluated on $\bar B(z,r)$; the hypothesis is the natural-number inequality `2*a ≤ Module.finrank ℝ E - 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Spheres.lean#L158-L178

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

theorem OAI.SubsphereRegression.terminal_cap_mass [Nontrivial E] (y z : E) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (a : ℕ) (ha : 2*a ≤ Module.finrank ℝ E - 1) :
    ((ambientSphereLaw (E := E)).restrict (Metric.closedBall y ε)) (Metric.closedBall z r) ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) *
        ENNReal.ofReal (ε^a) * ENNReal.ofReal (r^a) := by sorry
