-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_sphereLaw_cap_raw
-- name    : OAI.SubsphereRegression.sphereLaw_cap_raw
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:22:57.308853+00:00
-- url     : https://prove2.me/theorems/9779c14c-6640-4af1-88c7-bce4db229097
-- title:
--   Spherical caps of radius $r$ have normalized measure at most $3\cdot 4^d r^{d-1}$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $d\ge1$ with its Borel $\sigma$-algebra and its Lebesgue measure $\lambda_E$ (the Haar measure giving the cube spanned by an orthonormal basis volume $1$). Let $S=\{x\in E:\|x\|=1\}$ be the unit sphere, and let $\sigma_E$ be the normalized surface measure on $S$: the surface measure induced by $\lambda_E$, for which a measurable $s\subseteq S$ has measure $d\cdot\lambda_E\bigl((0,1)\cdot s\bigr)$, divided by its total mass, so that $\sigma_E$ is a probability measure. Here $(0,1)\cdot s=\{cx:0<c<1,\ x\in s\}$.
--
--   Let $z\in E$ be an arbitrary point (it need not lie on the sphere) and let $0<r\le1$. Then the set of unit vectors within Euclidean distance $r$ of $z$ satisfies
--   $$\sigma_E\bigl(\{x\in S:\ \|x-z\|\le r\}\bigr)\;\le\;3\cdot4^{d}\,r^{\,d-1}.$$
--
--   This is a polynomial small-ball estimate for the uniform measure on the sphere, with the sharp exponent $d-1$ (the dimension of the sphere) and an explicit constant exponential in $d$. It is the basic input for the local mass bounds of the uniform sphere measure regarded as a measure on $E$.
--
--   **Formalization Note** The statement assumes both that $E$ is nontrivial and that $1\le d$ (the second follows from the first); the exponent is the natural-number difference $d-1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Spheres.lean#L85-L115

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

theorem OAI.SubsphereRegression.sphereLaw_cap_raw [Nontrivial E] (z : E) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hd : 1 ≤ Module.finrank ℝ E) :
    sphereLaw {s : Metric.sphere (0 : E) 1 | dist s.val z ≤ r} ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) *
        ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) := by sorry
