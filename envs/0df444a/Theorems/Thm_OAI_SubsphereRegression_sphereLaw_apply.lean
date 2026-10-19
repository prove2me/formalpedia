-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_sphereLaw_apply
-- name    : OAI.SubsphereRegression.sphereLaw_apply
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:21:09.139651+00:00
-- url     : https://prove2.me/theorems/13bd8318-ffb9-41e6-8252-6f7f92241acd
-- title:
--   Normalized sphere measure of a set equals the uniform ball measure of its open cone
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $d\ge1$ with its Borel $\sigma$-algebra and its Lebesgue measure $\lambda_E$ (the Haar measure giving the cube spanned by an orthonormal basis volume $1$). Let $S=\{x\in E:\|x\|=1\}$ be the unit sphere, and let $\sigma_E$ be the normalized surface measure on $S$: the surface measure induced by $\lambda_E$, for which a measurable $s\subseteq S$ has measure $d\cdot\lambda_E\bigl((0,1)\cdot s\bigr)$, divided by its total mass, so that $\sigma_E$ is a probability measure. Here $(0,1)\cdot s=\{cx:0<c<1,\ x\in s\}$. Let $B(0,1)$ and $\bar B(0,1)$ be the open and closed unit balls, and let $U_E$ be the uniform probability measure on the closed unit ball, $U_E(A)=\lambda_E\bigl(A\cap\bar B(0,1)\bigr)/\lambda_E\bigl(B(0,1)\bigr)$ for Borel $A\subseteq E$.
--
--   Then for every measurable set $s\subseteq S$,
--   $$\sigma_E(s)=U_E\bigl((0,1)\cdot s\bigr).$$
--
--   This expresses the uniform measure on the sphere through the uniform measure on the ball: a set of directions has the same probability as the open cone it spans inside the unit ball. It reduces estimates for the sphere measure, such as cap bounds and rotation invariance, to the corresponding facts about the Lebesgue measure.
--
--   **Formalization Note** $\sigma_E$ is `sphereLaw`, defined as `(volume.toSphere univ)⁻¹ • volume.toSphere`, and $U_E$ is `unitBallLaw`, the closed-ball restriction of `volume` scaled by the inverse volume of the open unit ball. $E$ is assumed nontrivial, i.e. $d\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Spheres.lean#L63-L83

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

theorem OAI.SubsphereRegression.sphereLaw_apply [Nontrivial E] {s : Set (Metric.sphere (0 : E) 1)}
    (hs : MeasurableSet s) :
    sphereLaw s = unitBallLaw (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by sorry
