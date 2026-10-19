-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_projectionSmoothing_moment
-- name    : OAI.SubsphereRegression.projectionSmoothing_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:14:08.313975+00:00
-- url     : https://prove2.me/theorems/3f8562b6-b042-4f86-a39a-2527ab96331d
-- title:
--   Noise-independent moment bound for the mollified projection density of a Frostman-type measure
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $d$, with its Borel $\sigma$-algebra, and let $\gamma_E$ be the standard Gaussian measure on $E$ (its coordinates in any orthonormal basis are independent standard normal variables). For $m\ge0$ write $\lambda_m$ for Lebesgue measure on $\mathbb{R}^m$, and let $R_m=\gamma_E^{\otimes m}\otimes\lambda_m$ be the reference measure on $E^m\times\mathbb{R}^m$ (a matrix of $m$ independent Gaussian rows $A_1,\dots,A_m\in E$ and a label vector $y\in\mathbb{R}^m$).
--
--   Let $\nu$ be a finite Borel measure on $E$ whose support lies in the closed unit ball $\bar B(0,1)$, and let $a\in\mathbb{R}$ be such that $\nu$ satisfies the local mass bound with exponent $a$: $\nu(\bar B(t,r))\le r^{a}$ for every $t\in\operatorname{supp}\nu$ and every $r>0$. Let $\varphi:\mathbb{R}\to[0,\infty]$ be measurable with $\int_{\mathbb{R}}\varphi(x)\,dx=1$, and let $m,n\ge0$ be integers with $n+m\le a$. Define the mollified projection density and the constant
--   $$P_{\nu,\varphi}(A,y)=\int_E\prod_{j=1}^{m}\varphi\bigl(y_j-\langle t,A_j\rangle\bigr)\,d\nu(t),\qquad K(\nu,a,m)=\nu(E)+3^{d}\,4^{a}\,2^{m+1}.$$
--   Then
--   $$\int_{E^m\times\mathbb{R}^m}P_{\nu,\varphi}(A,y)^{\,n+1}\,dR_m(A,y)\;\le\;\nu(E)\,K(\nu,a,m)^{n}.$$
--
--   When $\varphi$ is a centered normal density, $P_{\nu,\varphi}$ is the density with respect to $R_m$ of the rows together with the noisy labels $\langle t,A_j\rangle+\text{noise}$, with $t$ distributed according to $\nu$. The bound holds for every normalized nonnegative mollifier $\varphi$, so the constant does not depend on the noise level; this is what allows the noise to be sent to zero afterwards. Combined with Hölder's inequality it shows that rows and labels cannot concentrate on sets of small reference measure when $\nu$ is spread out in the sense of the local mass bound.
--
--   **Formalization Note** The density is `projectionSmoothing ν φ m`, the constant is `replicaConstant ν a m`, and the hypothesis is `HasLocalMassBound ν a`, which asks the ball inequality only for centres in the support ($r^a$ is a real power, embedded in $[0,\infty]$). All integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions, and $4^{a}$ is a real power.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Gaussian.lean#L271-L296

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.projectionSmoothing_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1)
    (m n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ z : (Fin m → E) × (Fin m → ℝ),
      (projectionSmoothing ν φ m z)^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
       ν Set.univ * (replicaConstant ν a m)^n := by sorry
