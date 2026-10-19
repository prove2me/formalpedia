-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_HasLocalMassBound_affine_tube
-- name    : OAI.SubsphereRegression.HasLocalMassBound.affine_tube
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:09:36.58774+00:00
-- url     : https://prove2.me/theorems/720627d3-3c52-402e-8a69-7e03d2c301c4
-- title:
--   Mass of a tube around an affine subspace under a local mass bound
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $\nu$ be a measure on $E$ and let $a\in\mathbb{R}$. We say that $\nu$ satisfies the *local mass bound with exponent $a$* if $\nu(\bar B(t,r))\le r^{a}$ for every $t\in\operatorname{supp}\nu$ and every $r>0$, where $\bar B(t,r)$ is the closed ball of radius $r$ about $t$ and $\operatorname{supp}\nu$ is the support of $\nu$ (the set of points all of whose neighbourhoods have positive $\nu$-measure).
--
--   Assume that $\nu$ satisfies the local mass bound with exponent $a$ and that its support lies in the closed unit ball, $\operatorname{supp}\nu\subseteq\bar B(0,1)$. Let $L$ be a nonempty affine subspace of $E$ with direction $\vec L$, put $\ell=\dim\vec L$, and write $\operatorname{dist}(t,L)=\inf_{q\in L}\|t-q\|$. Then for every $0<r\le1$,
--   $$\nu\bigl(\{t\in E:\operatorname{dist}(t,L)\le r\}\bigr)\le\left(\frac{3}{r}\right)^{\ell}(4r)^{a}.$$
--
--   The right-hand side equals $3^{\ell}4^{a}r^{a-\ell}$, which tends to $0$ as $r\to0$ when $a>\ell$: a measure that is $a$-dimensional in the sense of the local mass bound gives small mass to thin neighbourhoods of affine subspaces of dimension less than $a$. This tube estimate is the basis for showing that such affine subspaces are null and for bounding inverse moments of the distance to them, which in turn control negative moments of Gram determinants of independent samples.
--
--   **Formalization Note** The predicate is `HasLocalMassBound ν a` and the bound is `ENNReal.ofReal ((3 / r) ^ Module.finrank ℝ L.direction * (4 * r) ^ a)`, where the first power has a natural-number exponent and `(4 * r) ^ a` is the real power `Real.rpow`. The measure $\nu$ is not assumed to be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Geometry.lean#L299-L328

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

theorem OAI.SubsphereRegression.HasLocalMassBound.affine_tube {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L] {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ν {t | Metric.infDist t L ≤ r} ≤
      ENNReal.ofReal ((3 / r) ^ Module.finrank ℝ L.direction * (4 * r) ^ a) := by sorry
