-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_HasLocalMassBound_affine_null
-- name    : OAI.SubsphereRegression.HasLocalMassBound.affine_null
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:10:00.378014+00:00
-- url     : https://prove2.me/theorems/25a74ca3-ffe6-4882-8144-266949fc94a2
-- title:
--   Affine subspaces of dimension at most $a-1$ are null under a local mass bound with exponent $a$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $\nu$ be a measure on $E$ and let $a\in\mathbb{R}$. We say that $\nu$ satisfies the *local mass bound with exponent $a$* if $\nu(\bar B(t,r))\le r^{a}$ for every $t\in\operatorname{supp}\nu$ and every $r>0$, where $\bar B(t,r)$ is the closed ball of radius $r$ about $t$ and $\operatorname{supp}\nu$ is the support of $\nu$ (the set of points all of whose neighbourhoods have positive $\nu$-measure).
--
--   Assume that $\nu$ satisfies the local mass bound with exponent $a$ and that $\operatorname{supp}\nu\subseteq\bar B(0,1)$. Let $L$ be a nonempty affine subspace of $E$ whose direction $\vec L$ (the linear subspace of differences of points of $L$) satisfies
--   $$\dim\vec L+1\le a.$$
--   Then
--   $$\nu(L)=0.$$
--
--   So a measure that is $a$-dimensional in the sense of the local mass bound does not charge affine subspaces of dimension at most $a-1$. Applied to the affine span of finitely many previously drawn points, this is the step showing that independent samples from such a measure are almost surely in general position as long as their number does not exceed the exponent.
--
--   **Formalization Note** The predicate is `HasLocalMassBound ν a`; the hypothesis reads `(Module.finrank ℝ L.direction : ℝ) + 1 ≤ a`, and $\nu(L)$ is the measure of the underlying set of `L`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Geometry.lean#L367-L392

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
open EuclideanGeometry

theorem OAI.SubsphereRegression.HasLocalMassBound.affine_null {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L]
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + 1 ≤ a) : ν L = 0 := by sorry
