-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_measurable_finiteSample
-- name    : OAI.SubsphereCurrent.measurable_finiteSample
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:42:49.058004+00:00
-- url     : https://prove2.me/theorems/0a4bd1ec-ea07-44a6-b213-47df99c4fec1
-- title:
--   Measurability of the inverse-CDF sampler in its parameters
-- statement:
--   Let $(X,\mathcal{A})$ be a measurable space and $n\ge1$, and give $[n]=\{0,1,\dots,n-1\}$ the discrete $\sigma$-algebra. For a probability mass function $p$ on $[n]$ write $F_p(k)=\sum_{0\le j<\min(k,n)}p(j)$ for its cumulative sums and $S_p:\mathbb{R}\to[n]$ for the inverse-CDF sampler: $S_p(r)$ is an index $j$ with $F_p(j)\le r<F_p(j+1)$ if one exists, and $0$ otherwise.
--
--   **Theorem.** Let $x\mapsto p_x$ be a family of probability mass functions on $[n]$, indexed by $x\in X$, such that for every $i\in[n]$ the map $x\mapsto p_x(i)\in[0,\infty]$ is measurable, and let $r:X\to\mathbb{R}$ be measurable. Then the map
--   $$
--   X\to[n],\qquad x\longmapsto S_{p_x}\bigl(r(x)\bigr)
--   $$
--   is measurable.
--
--   So drawing a finite random choice by feeding a measurable coin into a measurably varying distribution is a measurable operation. This is what allows a randomized finite-state transition to be rewritten as a deterministic, still measurable, function of the observation and an auxiliary uniform coin.
--
--   **Formalization Note** The family is `p : X -> PMF (Fin n)`, and the hypothesis asks that each coordinate `fun x => p x i` be measurable as a map into the extended nonnegative reals; the sampler is `finiteSample`, and the instance `[NeZero n]` encodes $n\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Kernels/Precision.lean#L207-L221

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

open OAI OAI.SubsphereCurrent
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

theorem OAI.SubsphereCurrent.measurable_finiteSample {X : Type*} [MeasurableSpace X] {n : ℕ} [NeZero n]
    {p : X → PMF (Fin n)} {r : X → ℝ}
    (hp : ∀ i, Measurable (fun x => p x i)) (hr : Measurable r) :
    Measurable (fun x => finiteSample (p x) (r x)) := by sorry
