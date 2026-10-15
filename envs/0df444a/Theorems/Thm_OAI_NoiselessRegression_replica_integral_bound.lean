-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_replica_integral_bound
-- name    : OAI.NoiselessRegression.replica_integral_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:25:51.500085+00:00
-- url     : https://prove2.me/theorems/4d623c40-437c-408b-9edf-cfff1dac8e13
-- title:
--   Inverse Gram–Schmidt moments of independent samples from a measure with a local mass bound
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra. For $w=(w_0,\dots,w_{n-1})\in E^{n}$ let $u_0(w),\dots,u_{n-1}(w)$ be its Gram–Schmidt vectors, $u_j(w)=w_j-\sum_{i<j}\frac{\langle u_i(w),w_j\rangle}{\|u_i(w)\|^{2}}u_i(w)$ (terms with $u_i(w)=0$ omitted). For $m\in\mathbb{N}$ and a base point $p\in E$, the replica weight of $v\in E^{n}$ is
--   $$W_{m,p}(v)=\prod_{i=0}^{n-1}\big\|u_i(v_0-p,\dots,v_{n-1}-p)\big\|^{-m}\in[0,\infty),$$
--   with the convention $0^{-1}=0$. Here $\|u_i(v-p)\|$ is the distance from $v_i$ to the affine hull of $p,v_0,\dots,v_{i-1}$.
--
--   Let $\nu$ be a finite measure on $E$ and $a\in\mathbb{R}$, and assume that
--
--   - $\nu$ has a local mass bound with exponent $a$: $\nu(\bar B(t,r))\le r^{a}$ for every $t$ in the support of $\nu$ and every $r>0$, where $\bar B(t,r)$ is the closed ball;
--   - the support of $\nu$ (the set of points all of whose open neighbourhoods have positive measure) is contained in the closed unit ball $\bar B(0,1)$.
--
--   Let $m,n\in\mathbb{N}$ with $n+m\le a$, and let $p\in E$. Then
--   $$
--   \int_{E^{n}}W_{m,p}(v)\,d\nu^{\otimes n}(v)\ \le\ \Big(\nu(E)+3^{\dim E}\,4^{a}\,2^{m+1}\Big)^{n},
--   $$
--   where $\nu^{\otimes n}$ is the $n$-fold product measure on $E^{n}$.
--
--   For affinely independent $p,v_0,\dots,v_{n-1}$, the product of the norms $\|u_i(v-p)\|$ is the $n$-dimensional volume of the parallelotope spanned by $v_0-p,\dots,v_{n-1}-p$. The theorem therefore bounds negative moments of the volume spanned by $n$ independent samples ("replicas") from $\nu$, uniformly in the base point $p$. Such bounds control the moments of noise-smoothed densities of Gaussian projections of $\nu$, which in turn compare the law of noiseless linear observations of a random vector with a Gaussian reference measure.
--
--   **Formalization Note** The left-hand side is `∫⁻ v, replicaWeight m p v ∂Measure.pi (fun _ => ν)` and the base of the power is `replicaConstant ν a m`, computed in $[0,\infty]$ with the real power $4^{a}$ embedded by `ENNReal.ofReal`. The factor $\|u_i\|^{-m}$ is `ENNReal.ofReal` of the $m$-th power of the real inverse of $\|u_i\|$, so a vanishing Gram–Schmidt vector contributes the factor $0$ when $m\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/ReplicaMoments.lean#L60-L93

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.NoiselessRegression.replica_integral_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (m : ℕ) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ v : Fin n → E, replicaWeight m p v ∂Measure.pi (fun _ => ν) ≤
      (replicaConstant ν a m) ^ n := by sorry
