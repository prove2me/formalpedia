-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Polar_measurable_radial
-- name    : OAI.SubsphereCurrent.Polar.measurable_radial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:49:51.135044+00:00
-- url     : https://prove2.me/theorems/284f98be-d44e-4b66-ab73-59777285451c
-- title:
--   Measurability of the radial extension of a function on the unit sphere
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $S(E)=\{x\in E:\lVert x\rVert=1\}$ be its unit sphere with the subspace $\sigma$-algebra, and let $g:S(E)\to[0,\infty]$. The *radial extension* of $g$ is the function $\mathrm{rad}\,g:E\to[0,\infty]$ that is constant along each open ray from the origin and vanishes at the origin:
--   $$
--   (\mathrm{rad}\,g)(x)=\begin{cases}g\bigl(x/\lVert x\rVert\bigr), & x\neq0,\\ 0, & x=0.\end{cases}
--   $$
--
--   **Theorem.** If $g$ is measurable, then $\mathrm{rad}\,g$ is measurable.
--
--   Radial extensions are how integrals over the sphere are compared with volume integrals over balls in polar coordinates; this lemma provides the measurability needed to apply Tonelli's theorem and the polar change of variables to them. No assumption $E\neq0$ is needed (for $E=0$ the extension is identically $0$).
--
--   **Formalization Note** The extension is `Polar.radial g`, defined by a dependent `if` on `x = 0` and the normalization `NormedSpace.normalize x`. The section's assumption that $E$ is nontrivial is omitted for this lemma.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Geometry/Integration.lean#L60-L75

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

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Polar
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [Nontrivial E] in
theorem OAI.SubsphereCurrent.Polar.measurable_radial {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g) :
    Measurable (radial g) := by sorry
