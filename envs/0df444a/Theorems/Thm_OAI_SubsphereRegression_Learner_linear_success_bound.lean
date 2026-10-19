-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_Learner_linear_success_bound
-- name    : OAI.SubsphereRegression.Learner.linear_success_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:31:11.462382+00:00
-- url     : https://prove2.me/theorems/a9c5cf72-0d8a-4a2e-86e1-05d05f590d89
-- title:
--   One-pass learners with at most $d/4$ Gaussian samples recover a random direction with probability at most $21/32$
-- statement:
--   Fix integers $d,M,T\ge0$, a measurable space $\Omega$ of random seeds with a probability measure $\rho$, and let $Q=\{0,1,\dots,2^M-1\}$ be a set of $2^M$ memory states. Let $S^{d-1}\subset\mathbb{R}^d$ be the unit sphere with its normalized surface measure $\sigma_d$, and let $\gamma_d$ be the standard Gaussian measure on $\mathbb{R}^d$.
--
--   A learner $L$ consists of an initial rule $\omega\mapsto(b_0,q_0)$, transition rules $(t,\omega,q,(x,y))\mapsto(b,q')$ and output rules $(t,\omega,q)\mapsto\hat s\in S^{d-1}$, where $b\in\{\text{stop},\text{continue}\}$ and $q,q'\in Q$. On an unknown unit vector $s$ and samples $x_1,\dots,x_T\in\mathbb{R}^d$, it starts in state $q_0$, or stops at time $0$ if $b_0$ is stop. At each step $t=1,\dots,T$, if it has not stopped, it reads the observation $(x_t,\langle x_t,s\rangle)$ and applies the $t$-th transition rule, stopping at the first step whose rule says stop. Its estimate $\hat s(s,\omega,x)$ is the output rule applied to the stopping time (or to $T$ if it never stops), the seed and the final state. The learner is admissible if the initial rule and each output rule are $\rho$-almost-everywhere measurable in $\omega$, each transition rule is almost-everywhere measurable in $(\omega,(x,y))$ for $\rho\otimes(\gamma_d\otimes\lambda_1)$ with $\lambda_1$ Lebesgue measure on labels, the estimate $(\omega,x)\mapsto\hat s(s,\omega,x)$ is almost-everywhere measurable for $\rho\otimes\gamma_d^{\otimes T}$ for each fixed $s$, and $(s,\omega,x)\mapsto\hat s(s,\omega,x)$ is almost-everywhere measurable for $\sigma_d\otimes\rho\otimes\gamma_d^{\otimes T}$.
--
--   Let $\varepsilon\in\mathbb{R}$, and assume $d\ge1$, $4T\le d$, $\varepsilon\le1/10$, and that $L$ is admissible. Then, with $s\sim\sigma_d$, $\omega\sim\rho$ and $x_1,\dots,x_T$ independent with law $\gamma_d$, the uniform success probability satisfies
--   $$\Pr\Bigl[\arccos\bigl\langle\hat s(s,\omega,x),s\bigr\rangle\le\varepsilon\Bigr]\;\le\;\frac{21}{32}.$$
--
--   The bound does not depend on the memory size $M$: with at most $d/4$ samples, no learner of this form, however many states it has, recovers a uniformly random direction to angular accuracy $1/10$ with probability above $21/32$. In particular no such learner reaches uniform success probability $2/3$ with $T\le d/4$.
--
--   **Formalization Note** The learner is `Learner d M T Ω` with `Admissible`, and the probability is `L.uniformSuccess ρ ε`, the product measure `(uniformSphere d).prod (ρ.prod (sampleLaw d T))` of the success set $\{\text{angularError}\le\varepsilon\}$. The angular error is `Real.arccos` of the inner product, and no lower bound on $\varepsilon$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Blocks.lean#L46-L90

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

open OAI OAI.SubsphereRegression OAI.SubsphereRegression.Learner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
open scoped Pointwise

theorem OAI.SubsphereRegression.Learner.linear_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 0 < d) (hT : 4*T ≤ d) {ε : ℝ} (hε : ε ≤ 1/10) (hL : L.Admissible ρ) :
    L.uniformSuccess ρ ε ≤ ENNReal.ofReal (21/32 : ℝ) := by sorry
