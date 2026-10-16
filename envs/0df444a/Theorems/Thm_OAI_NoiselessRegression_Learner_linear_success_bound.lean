-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_Learner_linear_success_bound
-- name    : OAI.NoiselessRegression.Learner.linear_success_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:47:04.078843+00:00
-- url     : https://prove2.me/theorems/f27a7f58-452a-4d2e-848c-27e5694efe33
-- title:
--   With at most $d/4$ noiseless Gaussian samples, uniform-prior success at angular accuracy $\varepsilon\le1/10$ is at most $21/32$
-- statement:
--   Fix $d,M,T\in\mathbb N$. Write $S^{d-1}=\{u\in\mathbb R^d:\|u\|=1\}$ for the Euclidean unit sphere, $\langle\cdot,\cdot\rangle$ for the standard inner product, and $\mathcal Q=\{0,1,\dots,2^M-1\}$ for the set of $2^M$ memory states. Let $(\Omega,\mathcal F)$ be a measurable space of internal randomness. A *learner* $L$ consists of an initial choice $\iota:\Omega\to\{\mathrm{stop},\mathrm{go}\}\times\mathcal Q$, transitions $\tau_t:\Omega\times\mathcal Q\times(\mathbb R^d\times\mathbb R)\to\{\mathrm{stop},\mathrm{go}\}\times\mathcal Q$ and outputs $o_t:\Omega\times\mathcal Q\to S^{d-1}$ for $t\in\mathbb N$. Given an unknown $s\in S^{d-1}$, randomness $\omega\in\Omega$ and samples $x=(x_1,\dots,x_T)\in(\mathbb R^d)^T$, the learner starts in the state $b_0$ given by $\iota(\omega)$ and stops at time $0$ if $\iota(\omega)$ says stop. At each step $t=1,\dots,T$ at which it has not stopped, it reads the row $x_t$ with its noiseless label $\langle x_t,s\rangle$, and $\tau_t\bigl(\omega,b_{t-1},(x_t,\langle x_t,s\rangle)\bigr)$ gives the new state $b_t$ and decides whether to stop at time $t$. If it never stops, the run ends at time $T$. If $t^{\ast}$ is the stopping time and $b_{t^{\ast}}$ the state at that time, the estimate is $\hat s_L(s,\omega,x)=o_{t^{\ast}}(\omega,b_{t^{\ast}})\in S^{d-1}$, and its angular error is $\arccos\langle\hat s_L(s,\omega,x),s\rangle$.
--
--   Let $\sigma_d$ be the uniform probability measure on $S^{d-1}$ (normalized surface measure), $\gamma_d$ the standard Gaussian measure on $\mathbb R^d$, $P_T=\gamma_d^{\otimes T}$ the law of $T$ independent standard Gaussian rows, $\lambda$ Lebesgue measure on $\mathbb R$, and $\rho$ a probability measure on $\Omega$. The learner is *admissible* for $\rho$ if $\iota$ is $\rho$-a.e. measurable; for every $t$ and $b\in\mathcal Q$ the map $(\omega,(x,y))\mapsto\tau_t(\omega,b,(x,y))$ is a.e. measurable for $\rho\otimes(\gamma_d\otimes\lambda)$ and $o_t(\cdot,b)$ is $\rho$-a.e. measurable; for every $s$ the map $(\omega,x)\mapsto\hat s_L(s,\omega,x)$ is $\rho\otimes P_T$-a.e. measurable; and $(s,\omega,x)\mapsto\hat s_L(s,\omega,x)$ is $\sigma_d\otimes\rho\otimes P_T$-a.e. measurable. For $\varepsilon\in\mathbb R$ the *uniform-prior success probability* is $\mathrm{Succ}(L,\rho,\varepsilon)=(\sigma_d\otimes\rho\otimes P_T)\bigl\{(s,\omega,x):\arccos\langle\hat s_L(s,\omega,x),s\rangle\le\varepsilon\bigr\}$, the probability that the angular error is at most $\varepsilon$ when $s$ is uniform on the sphere and independent of $\omega\sim\rho$ and $x\sim P_T$.
--
--   Assume $d>0$, $4T\le d$ and $\varepsilon\le1/10$, and let $L$ be admissible for the probability measure $\rho$. Then
--
--   $$
--   \mathrm{Succ}(L,\rho,\varepsilon)\le\frac{21}{32}.
--   $$
--
--   Since $21/32<2/3$, an admissible learner that succeeds with probability at least $2/3$ at an accuracy $\varepsilon\le1/10$ under the uniform prior must read more than $d/4$ samples, whatever its number of memory states and its internal randomness. This linear lower bound $T>d/4$ is the first step of the sample lower bound for finite-state learners.
--
--   **Formalization Note** The learner is `L : Learner d M T Ω` with states `Fin (2^M)` and stop flags in `Bool` (`true` means stop); $\mathrm{Succ}(L,\rho,\varepsilon)$ is `L.uniformSuccess ρ ε`, valued in $[0,\infty]$, where $\sigma_d$ is `uniformSphere d` (the surface measure `volume.toSphere` divided by its total mass) and $P_T$ is `sampleLaw d T`; admissibility is `L.Admissible ρ`. The bound is `ENNReal.ofReal (21/32)`. No sign condition on $\varepsilon$ is assumed; for $\varepsilon<0$ the success event is empty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Rotational.lean#L86-L130

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere
import Definitions.Def_OAI_Probability_GaussianRegression_Stream
import Definitions.Def_OAI_Probability_GaussianRegression_Caps
import Definitions.Def_OAI_Probability_GaussianRegression_Execution
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational

open OAI OAI.NoiselessRegression OAI.NoiselessRegression.Learner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise
universe u

theorem OAI.NoiselessRegression.Learner.linear_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 0 < d) (hT : 4*T ≤ d) {ε : ℝ} (hε : ε ≤ 1/10) (hL : L.Admissible ρ) :
    L.uniformSuccess ρ ε ≤ ENNReal.ofReal (21/32 : ℝ) := by sorry
