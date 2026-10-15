-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_HasLocalMassBound_any_center
-- name    : OAI.NoiselessRegression.HasLocalMassBound.any_center
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:21:24.897117+00:00
-- url     : https://prove2.me/theorems/814662b8-e30c-4180-8a5b-60f6a2a3e607
-- title:
--   A local mass bound at support points controls balls with arbitrary centers
-- statement:
--   Let $E$ be a finite-dimensional real normed space equipped with a $\sigma$-algebra, let $\nu$ be a measure on $E$ and let $a\in\mathbb{R}$. Write $\bar B(z,r)=\{x\in E:\|x-z\|\le r\}$ for the closed ball and $\operatorname{supp}\nu$ for the support of $\nu$, the set of points all of whose open neighbourhoods have positive $\nu$-measure. Say that $\nu$ has a *local mass bound with exponent $a$* if
--   $$
--   \nu\big(\bar B(t,r)\big)\le r^{a}\qquad\text{for all } t\in\operatorname{supp}\nu \text{ and all } r>0 .
--   $$
--
--   If $\nu$ has a local mass bound with exponent $a$, then for every center $z\in E$ and every radius $r>0$,
--   $$
--   \nu\big(\bar B(z,r)\big)\le (2r)^{a}.
--   $$
--
--   The defining condition only constrains balls centered in the support; this statement removes that restriction at the cost of doubling the radius. It is the form in which the local mass bound is applied to covers by balls whose centers are not known to lie in the support, for instance balls covering a thin tube around an affine subspace.
--
--   **Formalization Note** The hypothesis is `HasLocalMassBound ν a`. The Borel assumption of the ambient context is omitted, so no compatibility between the $\sigma$-algebra and the topology is required; for a non-measurable ball, $\nu$ is evaluated as an outer measure. Both sides live in $[0,\infty]$, the right-hand side being `ENNReal.ofReal ((2 * r) ^ a)` with the real power.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Nets.lean#L27-L42

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
theorem OAI.NoiselessRegression.HasLocalMassBound.any_center {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (z : E) {r : ℝ} (hr : 0 < r) :
    ν (Metric.closedBall z r) ≤ ENNReal.ofReal ((2 * r) ^ a) := by sorry
