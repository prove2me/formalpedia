-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_normalized_routing_bound
-- name    : OAI.SubsphereRegression.normalized_routing_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:31:48.19862+00:00
-- url     : https://prove2.me/theorems/22c7e40e-2b88-4c2d-bfa3-8dd100c57b32
-- title:
--   Routing bound for Gaussian projection laws of Frostman-type measures
-- statement:
--   Let $E$ be a real inner product space of finite dimension $d\ge1$ with its Borel $\sigma$-algebra, and let $\gamma_E$ be the standard Gaussian measure on $E$. For $m\in\mathbb{N}$, an *observation* is a pair $x=(A,b)\in E^m\times\mathbb{R}^m$ of $m$ rows $A_1,\dots,A_m\in E$ and $m$ labels. For a finite Borel measure $\nu$ on $E$, the *projection law* $P_{\nu,m}$ is the image of $\gamma_E^{\otimes m}\otimes\nu$ under $(A,t)\mapsto\bigl(A,(\langle t,A_i\rangle)_{i=1}^m\bigr)$: the (possibly unnormalized) joint law of $m$ independent standard Gaussian rows and their noiseless labels against a hidden vector $t$ drawn from $\nu$. We say that $\nu$ satisfies the *local mass bound with exponent $a$* if $\nu(\bar B(t,r))\le r^{a}$ for every point $t$ of the support of $\nu$ and every $r>0$, where $\bar B(t,r)$ denotes the closed ball.
--
--   Let $a,m,n\in\mathbb{N}$ satisfy $a\le d$, $m\le d$, $n\ge1$ and $n+m\le a$. Let $J$ be a finite set carrying a $\sigma$-algebra in which singletons are measurable, and for each $j\in J$ let $\nu_j$ be a finite Borel measure on $E$ such that (i) $\nu_j$ satisfies the local mass bound with exponent $a$, (ii) $\nu_j(E)\le1$, and (iii) the support of $\nu_j$ is contained in the closed unit ball $\bar B(0,1)$. Then for every measurable map $\varphi:E^m\times\mathbb{R}^m\to J$,
--
--   $$
--   \sum_{j\in J}P_{\nu_j,m}\bigl(\{x\in E^m\times\mathbb{R}^m:\varphi(x)=j\}\bigr)\;\le\;32768^{d}\,|J|^{1/(n+1)} .
--   $$
--
--   Think of $\varphi$ as the rule by which a learner with state set $J$ chooses its next state after reading a block of $m$ labelled Gaussian rows, and of $\nu_j$ as the part of the prior on the hidden vector for which state $j$ is the desired outcome. Each summand is at most $\nu_j(E)\le1$, so the trivial bound is $|J|$; the theorem reduces the dependence on the number of states to $|J|^{1/(n+1)}$ at the price of the factor $32768^d=2^{15d}$. This one-block estimate is the basic step of the memory–sample lower bound for recovering a hidden unit vector from labelled Gaussian rows; a rescaled version handles measures with polynomial ball growth.
--
--   **Formalization Note** Measures take values in $[0,\infty]$ and the inequality is between extended nonnegative reals; $|J|^{1/(n+1)}$ is a real power. The local mass bound is `HasLocalMassBound (ν j) a` (with $a$ cast to a real exponent), the projection law is `projectionLaw (ν j) m`, and $\gamma_E$ is Mathlib's `stdGaussian E`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Blocks.lean#L220-L277

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

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.normalized_routing_bound {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (ν : J → Measure E) [∀ j, IsFiniteMeasure (ν j)]
    {a m n : ℕ} (hν : ∀ j, HasLocalMassBound (ν j) (a : ℝ))
    (hν1 : ∀ j, ν j univ ≤ 1) (hsupport : ∀ j, (ν j).support ⊆ Metric.closedBall 0 1)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hn : 1 ≤ n) (hmargin : n+m ≤ a)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (hφ : Measurable φ) :
    (∑ j, projectionLaw (ν j) m {x | φ x = j}) ≤
      (32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) := by sorry
