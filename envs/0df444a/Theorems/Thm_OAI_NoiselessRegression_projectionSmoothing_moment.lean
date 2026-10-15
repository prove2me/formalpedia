-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_projectionSmoothing_moment
-- name    : OAI.NoiselessRegression.projectionSmoothing_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:26:38.788087+00:00
-- url     : https://prove2.me/theorems/0531248c-e524-4a06-ac1e-688dcbaf9c10
-- title:
--   Moment bound for the Gaussian projection smoothing of a measure with a local mass bound
-- statement:
--   Let $E$ be a real inner product space of finite dimension $d$ with its Borel $\sigma$-algebra, let $\gamma_E$ be the standard Gaussian measure on $E$, and let $\lambda_m$ be Lebesgue measure on $\mathbb R^m$. Let $\nu$ be a finite Borel measure on $E$ whose support $\operatorname{supp}\nu$ is contained in the closed unit ball $\bar B(0,1)$ and which satisfies a local mass bound with exponent $a\in\mathbb R$: $\nu\big(\bar B(t,r)\big)\le r^{a}$ for every $t\in\operatorname{supp}\nu$ and every $r>0$. Let $\varphi:\mathbb R\to[0,\infty]$ be measurable with $\int_{\mathbb R}\varphi(z)\,dz=1$.
--
--   For $m\in\mathbb N$, the projection smoothing of $\nu$ by $\varphi$ is the function on $E^m\times\mathbb R^m$ given by
--   $$
--   S_{\nu,\varphi}(A,y)=\int_E\prod_{j=1}^{m}\varphi\big(y_j-\langle t,A_j\rangle\big)\,d\nu(t),\qquad A=(A_1,\dots,A_m)\in E^m,\ y\in\mathbb R^m,
--   $$
--   and the replica constant is $K_{\nu,a,m}=\nu(E)+3^{d}\,4^{a}\,2^{m+1}$. If $m,n\in\mathbb N$ satisfy $n+m\le a$, then
--   $$
--   \int_{E^m\times\mathbb R^m}S_{\nu,\varphi}(A,y)^{\,n+1}\,d\big(\gamma_E^{\otimes m}\otimes\lambda_m\big)(A,y)\;\le\;\nu(E)\,K_{\nu,a,m}^{\,n}.
--   $$
--
--   When $\nu$ is a prior on an unknown parameter $t$ and $\varphi$ is the density of independent label noise, $S_{\nu,\varphi}(A,\cdot)$ is the Lebesgue density of the noisy label vector $\big(\langle t,A_j\rangle+\text{noise}_j\big)_{j\le m}$ given the design $A$ (unnormalized if $\nu$ is not a probability measure). The theorem bounds the $(n+1)$-st moment of this density relative to the reference measure $\gamma_E^{\otimes m}\otimes\lambda_m$, uniformly in the noise density $\varphi$. This uniformity is what allows the noise level to be sent to zero when deriving Hölder-type bounds for the noiseless observation law.
--
--   **Formalization Note** The integral is a lower Lebesgue integral and all quantities lie in $[0,\infty]$. The support is Mathlib's `Measure.support`, the local mass bound is `HasLocalMassBound ν a` (with $r^a$ a real power), $S_{\nu,\varphi}$ is `projectionSmoothing ν φ m`, and $K_{\nu,a,m}$ is `replicaConstant ν a m`, in which $3^d4^a$ is a real number embedded in $[0,\infty]$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Smoothing.lean#L50-L73

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.NoiselessRegression.projectionSmoothing_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1)
    (m n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ z : (Fin m → E) × (Fin m → ℝ),
      (projectionSmoothing ν φ m z)^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
       ν Set.univ * (replicaConstant ν a m)^n := by sorry
