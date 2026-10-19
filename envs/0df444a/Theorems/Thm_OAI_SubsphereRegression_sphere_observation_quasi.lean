-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_sphere_observation_quasi
-- name    : OAI.SubsphereRegression.sphere_observation_quasi
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:36:47.807653+00:00
-- url     : https://prove2.me/theorems/9260bf6d-12ed-4a8a-b9d4-079dc03114ed
-- title:
--   A Gaussian row and its label against a uniform unit vector have an absolutely continuous joint law
-- statement:
--   Let $E$ be a nonzero real inner product space of finite dimension $d\ge3$ with its Borel $\sigma$-algebra, let $\gamma_E$ be its standard Gaussian measure, let $\sigma$ be the normalized surface (uniform probability) measure on the unit sphere $S=\{s\in E:\|s\|=1\}$, and let $\lambda$ be Lebesgue measure on $\mathbb{R}$. Consider the observation map
--
--   $$
--   \Psi:S\times E\to E\times\mathbb{R},\qquad \Psi(s,x)=\bigl(x,\langle s,x\rangle\bigr).
--   $$
--
--   Then $\Psi$ is quasi-measure-preserving from $\sigma\otimes\gamma_E$ to $\gamma_E\otimes\lambda$: it is measurable, and the image measure $(\sigma\otimes\gamma_E)\circ\Psi^{-1}$ is absolutely continuous with respect to $\gamma_E\otimes\lambda$. Equivalently, for every measurable $N\subseteq E\times\mathbb{R}$ with $(\gamma_E\otimes\lambda)(N)=0$,
--
--   $$
--   (\sigma\otimes\gamma_E)\bigl\{(s,x):(x,\langle s,x\rangle)\in N\bigr\}=0 .
--   $$
--
--   Thus the observation $(x,\langle s,x\rangle)$ seen by a learner, when the hidden vector $s$ is uniform on the sphere and the row $x$ is Gaussian, never charges sets that are null for the reference measure "Gaussian row, Lebesgue label". Consequently two transition rules that agree almost everywhere with respect to $\gamma_E\otimes\lambda$ act identically on almost every actual observation, which is what allows replacing almost-everywhere measurable rules by Borel ones.
--
--   **Formalization Note** The statement is `Measure.QuasiMeasurePreserving` for the observation map, from `sphereLaw.prod (stdGaussian E)` to `(stdGaussian E).prod volume`. The hypothesis that $E$ is nontrivial is stated separately, although it follows from $d\ge3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Streaming.lean#L415-L441

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

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.sphere_observation_quasi [Nontrivial E] (hd : 3 ≤ Module.finrank ℝ E) :
    Measure.QuasiMeasurePreserving
      (fun z : (Metric.sphere (0 : E) 1) × E => (z.2, ⟪z.1.val,z.2⟫))
      ((sphereLaw (E := E)).prod (stdGaussian E)) ((stdGaussian E).prod volume) := by sorry
