-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_ambientSphereLaw_closedBall
-- name    : OAI.NoiselessRegression.ambientSphereLaw_closedBall
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:32:34.300344+00:00
-- url     : https://prove2.me/theorems/ed431bab-eaa0-42ad-be56-4bf56068ab56
-- title:
--   Polynomial cap bound for the uniform measure on the sphere
-- statement:
--   Let $E$ be a nontrivial real inner product space of finite dimension $d\ge1$, and let $\bar\sigma$ be the uniform probability measure on the unit sphere $\mathbb S=\{x:\|x\|=1\}$, viewed as a Borel measure on $E$. Concretely, $\bar\sigma$ is the image under the inclusion $\mathbb S\hookrightarrow E$ of the normalized surface measure $\sigma$, for which $\sigma(s)=\mathrm{Vol}(\{rx:0<r<1,\ x\in s\})/\mathrm{Vol}(B(0,1))$. Then for every centre $z\in E$, every radius $r>0$ and every $k\in\mathbb N$ with $k\le d-1$,
--
--   $$
--   \bar\sigma\big(\bar B(z,r)\big)\;\le\;3\cdot4^{d}\,r^{k}.
--   $$
--
--   Thus every spherical cap of radius $r$ has mass at most $3\cdot4^d r^{d-1}$, and the bound may be weakened to any exponent $k\le d-1$; for $r\ge1$ it holds trivially because $\bar\sigma$ is a probability measure. It is a polynomial (Frostman-type) mass bound for the sphere with an explicit constant exponential in $d$, used to show that observation laws built from a uniformly random unit vector are absolutely continuous and to bound the mass of small target caps.
--
--   **Formalization Note** $\bar\sigma$ is `ambientSphereLaw`, and $d-1$ is natural-number subtraction, which is the ordinary difference here since $d\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Sphere.lean#L138-L157

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
universe u
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.NoiselessRegression.ambientSphereLaw_closedBall [Nontrivial E] (z : E) {r : ℝ} (hr : 0 < r)
    (k : ℕ) (hk : k ≤ Module.finrank ℝ E - 1) :
    ambientSphereLaw (Metric.closedBall z r) ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) * ENNReal.ofReal (r^k) := by sorry
