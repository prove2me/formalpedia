-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_projectionLaw_set_bound
-- name    : OAI.SubsphereRegression.projectionLaw_set_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:19:07.379918+00:00
-- url     : https://prove2.me/theorems/1588f756-1efa-4273-bca8-12ed4436832d
-- title:
--   Set bound for the law of Gaussian rows with noiseless labels under a Frostman-type prior
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $d$, with its Borel $\sigma$-algebra, and let $\gamma_E$ be the standard Gaussian measure on $E$ (its coordinates in any orthonormal basis are independent standard normal variables). For $m\ge0$ write $\lambda_m$ for Lebesgue measure on $\mathbb{R}^m$, and let $R_m=\gamma_E^{\otimes m}\otimes\lambda_m$ be the reference measure on $E^m\times\mathbb{R}^m$. For a finite Borel measure $\nu$ on $E$, the projection law $\Pi_{\nu,m}$ is the image of $\gamma_E^{\otimes m}\otimes\nu$ under $(A,t)\mapsto\bigl(A,(\langle t,A_1\rangle,\dots,\langle t,A_m\rangle)\bigr)$: the joint law of $m$ independent Gaussian rows and the noiseless labels of a parameter $t\sim\nu$.
--
--   Assume that the support of $\nu$ lies in the closed unit ball $\bar B(0,1)$ and that, for some $a\in\mathbb{R}$, $\nu$ satisfies the local mass bound $\nu(\bar B(t,r))\le r^a$ for all $t\in\operatorname{supp}\nu$ and all $r>0$. Let $m\ge0$ and $n\ge1$ be integers with $n+m\le a$, and put $K(\nu,a,m)=\nu(E)+3^{d}\,4^{a}\,2^{m+1}$. Then for every subset $S\subseteq E^m\times\mathbb{R}^m$,
--   $$\Pi_{\nu,m}(S)\;\le\;\bigl(\nu(E)\,K(\nu,a,m)^{n}\bigr)^{\frac1{n+1}}\;R_m(S)^{1-\frac1{n+1}} .$$
--
--   The constant in front is finite, so in particular $\Pi_{\nu,m}$ is absolutely continuous with respect to $R_m$, with a quantitative modulus: observation sets of small reference measure are unlikely when the labels come from a spread-out prior. The exponent $n/(n+1)$ can be taken close to $1$ when the mass exponent $a$ exceeds the number $m$ of observations by a large margin.
--
--   **Formalization Note** The measures are `projectionLaw ν m` and `matrixLabelReference m`, and the hypothesis is `HasLocalMassBound ν a`. The set $S$ need not be measurable: Lean evaluates both measures on $S$ as outer measures. Powers with real exponents are taken in $[0,\infty]$, and $4^a$ is a real power.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Projection.lean#L95-L131

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.projectionLaw_set_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m n : ℕ) (hn : 1 ≤ n) (hmargin : (n : ℝ) + m ≤ a)
    (S : Set ((Fin m → E) × (Fin m → ℝ))) :
    projectionLaw ν m S ≤
      (ν Set.univ * (replicaConstant ν a m)^n)^(1 / ((n : ℝ) + 1)) *
      (matrixLabelReference (E := E) m S)^(1 - 1 / ((n : ℝ) + 1)) := by sorry
