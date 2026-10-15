-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_HasLocalMassBound_affine_null
-- name    : OAI.NoiselessRegression.HasLocalMassBound.affine_null
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:24:35.376593+00:00
-- url     : https://prove2.me/theorems/2e1fce9c-2e06-4e12-9eea-3c45963a6e83
-- title:
--   A measure on the unit ball with a strong local mass bound gives no mass to low-dimensional affine subspaces
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $\nu$ be a measure on $E$ and let $a\in\mathbb{R}$. Write $\bar B(z,r)=\{x\in E:\|x-z\|\le r\}$ and let $\operatorname{supp}\nu$ be the support of $\nu$, the set of points all of whose open neighbourhoods have positive measure. Assume:
--
--   1. $\nu$ has a local mass bound with exponent $a$, i.e. $\nu(\bar B(t,r))\le r^{a}$ for all $t\in\operatorname{supp}\nu$ and all $r>0$;
--   2. $\operatorname{supp}\nu\subseteq\bar B(0,1)$;
--   3. $L\subseteq E$ is a nonempty affine subspace whose direction $V$ (the linear subspace with $L=p+V$ for any $p\in L$) has dimension $\ell=\dim V$ satisfying $\ell+1\le a$.
--
--   Then
--   $$
--   \nu(L)=0 .
--   $$
--
--   Thus a measure on the unit ball whose balls of radius $r$ around support points have mass at most $r^{a}$ gives no mass to affine subspaces of dimension at most $a-1$. For independent samples from such a measure this implies that, almost surely, each new sample avoids the affine span of a base point and the previous samples, so that the samples are in general position as long as their number does not exceed $a$.
--
--   **Formalization Note** The subspace is an `AffineSubspace ℝ E` with a `Nonempty` instance, its dimension is `Module.finrank ℝ L.direction`, and $\nu(L)$ is the measure of the underlying set of $L$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/AffineTubes.lean#L123-L147

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
open EuclideanGeometry

theorem OAI.NoiselessRegression.HasLocalMassBound.affine_null {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L]
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + 1 ≤ a) : ν L = 0 := by sorry
