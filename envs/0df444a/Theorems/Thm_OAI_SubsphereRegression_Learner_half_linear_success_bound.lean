-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_Learner_half_linear_success_bound
-- name    : OAI.SubsphereRegression.Learner.half_linear_success_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T07:04:29.529891+00:00
-- url     : https://prove2.me/theorems/b50fbb63-7ea7-43ca-be47-0d36041ac878
-- title:
--   With at most $d/32$ Gaussian measurements no learner recovers a unit vector to angle $1/10$ with probability above $7/16$
-- statement:
--   Fix natural numbers $d$ (dimension), $M$ (memory bits) and $T$ (number of samples), and a measurable space $\Omega$ of random seeds with a probability measure $\rho$. Let $S^{d-1}$ be the unit sphere of $\mathbb R^d$ with its uniform (normalized surface) measure $\sigma_d$, let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$, $\lambda$ Lebesgue measure on $\mathbb R$, and $Q_M=\{0,1,\dots,2^M-1\}$ the set of memory states.
--
--   A *seeded one-pass learner* $L$ consists of an initial choice $\iota(\omega)\in\{\mathrm{stop},\mathrm{go}\}\times Q_M$, transitions $\tau_t(\omega,q,(x,y))\in\{\mathrm{stop},\mathrm{go}\}\times Q_M$ for $t\in\mathbb N$, $q\in Q_M$ and $(x,y)\in\mathbb R^d\times\mathbb R$, and outputs $o_t(\omega,q)\in S^{d-1}$. On a hidden direction $s\in S^{d-1}$, seed $\omega$ and rows $x_1,\dots,x_T\in\mathbb R^d$, it starts from $\iota(\omega)$ and, for $t=1,\dots,T$ as long as it has not stopped, replaces its state $q$ by the state part of $\tau_t(\omega,q,(x_t,\langle x_t,s\rangle))$, stopping at time $t$ if the flag is $\mathrm{stop}$. If it stops at time $t^*$ (possibly $0$) in state $q^*$, or reaches time $t^*=T$ in state $q^*$, its estimate is $\hat s(s,\omega,x)=o_{t^*}(\omega,q^*)$. Its *uniform success* at angular accuracy $\varepsilon$ is
--   $$\mathrm{US}(\varepsilon)=\big(\sigma_d\otimes\rho\otimes\gamma_d^{\otimes T}\big)\Big\{(s,\omega,x):\arccos\big\langle\hat s(s,\omega,x),s\big\rangle\le\varepsilon\Big\}.$$
--   The learner is *admissible* for $\rho$ if $\iota$ is $\rho$-a.e. measurable; for every $t$ and $q$ the map $(\omega,(x,y))\mapsto\tau_t(\omega,q,(x,y))$ is a.e. measurable for $\rho\otimes\gamma_d\otimes\lambda$; for every $t$ and $q$ the map $\omega\mapsto o_t(\omega,q)$ is $\rho$-a.e. measurable; for every $s$ the map $(\omega,x)\mapsto\hat s(s,\omega,x)$ is a.e. measurable for $\rho\otimes\gamma_d^{\otimes T}$; and $(s,\omega,x)\mapsto\hat s(s,\omega,x)$ is a.e. measurable for $\sigma_d\otimes\rho\otimes\gamma_d^{\otimes T}$.
--
--   **Theorem.** If $d\ge32$, $32T\le d$, $\varepsilon\le1/10$ and $L$ is admissible for the probability measure $\rho$, then
--
--   $$
--   \mathrm{US}(\varepsilon)\le\frac7{16}.
--   $$
--
--   No assumption is made on the memory size $M$: with at most $d/32$ noiseless linear measurements, no learner, however much memory it has, recovers a uniformly random unit vector to within angle $1/10$ with probability above $7/16$. In the half-precision lower bound, where uniform success at least $1/2$ is assumed, this disposes of the regime of very few samples: it forces $d\le32T$.
--
--   **Formalization Note** The model is `SubsphereRegression.Learner d M T Ω`, whose stop flag is a `Bool` (`true` means stop). Uniform success is the value of the product measure $\sigma_d\otimes(\rho\otimes\gamma_d^{\otimes T})$ on the success set, which the admissibility conditions make null-measurable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Estimates/HalfPrecision.lean#L126-L170

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
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine

open OAI OAI.SubsphereRegression OAI.SubsphereRegression.Learner
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.Learner.half_linear_success_bound {d M T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 32 ≤ d) (hT : 32*T ≤ d) {ε : ℝ} (hε : ε ≤ 1/10) (hL : L.Admissible ρ) :
    L.uniformSuccess ρ ε ≤ ENNReal.ofReal (7/16 : ℝ) := by sorry
