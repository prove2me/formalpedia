-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_HasLocalMassBound_any_center
-- name    : OAI.SubsphereRegression.HasLocalMassBound.any_center
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:02:59.59755+00:00
-- url     : https://prove2.me/theorems/cabe1107-0bca-4f20-b849-7df63a7399f2
-- title:
--   Local mass bounds extend to arbitrary centers after doubling the radius
-- statement:
--   Let $E$ be a finite-dimensional real normed space equipped with a $\sigma$-algebra, let $\nu$ be a measure on $E$ and let $a\in\mathbb{R}$. We say that $\nu$ satisfies the *local mass bound with exponent $a$* if
--   $$\nu\bigl(\bar B(t,r)\bigr)\le r^{a}\qquad\text{for every }t\in\operatorname{supp}\nu\text{ and every }r>0,$$
--   where $\bar B(t,r)=\{x\in E:\|x-t\|\le r\}$ is the closed ball and $\operatorname{supp}\nu$ is the support of $\nu$ (the set of points all of whose neighbourhoods have positive $\nu$-measure).
--
--   If $\nu$ satisfies the local mass bound with exponent $a$, then for every point $z\in E$, not necessarily in the support, and every $r>0$,
--   $$\nu\bigl(\bar B(z,r)\bigr)\le(2r)^{a}.$$
--
--   The hypothesis only controls balls centred on the support. This lemma removes that restriction at the cost of doubling the radius, which is what is needed when a set is covered by balls whose centres are produced by a geometric construction (for instance the points of a net), as in the estimates for tubes around affine subspaces. A typical example is the normalized Lebesgue measure on the unit ball of $E$, which satisfies the bound with $a=\dim E$.
--
--   **Formalization Note** The predicate is `HasLocalMassBound ν a`, and `r ^ a` is the real power `Real.rpow` embedded in $[0,\infty]$ by `ENNReal.ofReal`. The $\sigma$-algebra on $E$ need not be the Borel one (the section's `BorelSpace` assumption is omitted for this lemma), and $\nu$ is applied to balls as an outer measure, so no measurability is required. The support is Mathlib's `Measure.support`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Geometry.lean#L115-L130

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
theorem OAI.SubsphereRegression.HasLocalMassBound.any_center {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (z : E) {r : ℝ} (hr : 0 < r) :
    ν (Metric.closedBall z r) ≤ ENNReal.ofReal ((2 * r) ^ a) := by sorry
