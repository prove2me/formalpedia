-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_Learner_streaming_success_bound
-- name    : OAI.NoiselessRegression.Learner.streaming_success_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:47:49.630628+00:00
-- url     : https://prove2.me/theorems/e49050a1-f465-49c6-aef7-8fd976529c6b
-- title:
--   Uniform-prior success bound for a learner with $2^M$ memory states in noiseless Gaussian regression
-- statement:
--   Fix $d,M,T\in\mathbb N$. Write $S^{d-1}=\{u\in\mathbb R^d:\|u\|=1\}$ for the Euclidean unit sphere, $\langle\cdot,\cdot\rangle$ for the standard inner product, and $\mathcal Q=\{0,1,\dots,2^M-1\}$ for the set of $2^M$ memory states. Let $(\Omega,\mathcal F)$ be a measurable space of internal randomness. A *learner* $L$ consists of an initial choice $\iota:\Omega\to\{\mathrm{stop},\mathrm{go}\}\times\mathcal Q$, transitions $\tau_t:\Omega\times\mathcal Q\times(\mathbb R^d\times\mathbb R)\to\{\mathrm{stop},\mathrm{go}\}\times\mathcal Q$ and outputs $o_t:\Omega\times\mathcal Q\to S^{d-1}$ for $t\in\mathbb N$. Given an unknown $s\in S^{d-1}$, randomness $\omega\in\Omega$ and samples $x=(x_1,\dots,x_T)\in(\mathbb R^d)^T$, the learner starts in the state $b_0$ given by $\iota(\omega)$ and stops at time $0$ if $\iota(\omega)$ says stop. At each step $t=1,\dots,T$ at which it has not stopped, it reads the row $x_t$ with its noiseless label $\langle x_t,s\rangle$, and $\tau_t\bigl(\omega,b_{t-1},(x_t,\langle x_t,s\rangle)\bigr)$ gives the new state $b_t$ and decides whether to stop at time $t$. If it never stops, the run ends at time $T$. If $t^{\ast}$ is the stopping time and $b_{t^{\ast}}$ the state at that time, the estimate is $\hat s_L(s,\omega,x)=o_{t^{\ast}}(\omega,b_{t^{\ast}})\in S^{d-1}$, and its angular error is $\arccos\langle\hat s_L(s,\omega,x),s\rangle$.
--
--   Let $\sigma_d$ be the uniform probability measure on $S^{d-1}$ (normalized surface measure), $\gamma_d$ the standard Gaussian measure on $\mathbb R^d$, $P_T=\gamma_d^{\otimes T}$ the law of $T$ independent standard Gaussian rows, $\lambda$ Lebesgue measure on $\mathbb R$, and $\rho$ a probability measure on $\Omega$. The learner is *admissible* for $\rho$ if $\iota$ is $\rho$-a.e. measurable; for every $t$ and $b\in\mathcal Q$ the map $(\omega,(x,y))\mapsto\tau_t(\omega,b,(x,y))$ is a.e. measurable for $\rho\otimes(\gamma_d\otimes\lambda)$ and $o_t(\cdot,b)$ is $\rho$-a.e. measurable; for every $s$ the map $(\omega,x)\mapsto\hat s_L(s,\omega,x)$ is $\rho\otimes P_T$-a.e. measurable; and $(s,\omega,x)\mapsto\hat s_L(s,\omega,x)$ is $\sigma_d\otimes\rho\otimes P_T$-a.e. measurable. For $\varepsilon\in\mathbb R$ the *uniform-prior success probability* is $\mathrm{Succ}(L,\rho,\varepsilon)=(\sigma_d\otimes\rho\otimes P_T)\bigl\{(s,\omega,x):\arccos\langle\hat s_L(s,\omega,x),s\rangle\le\varepsilon\bigr\}$, the probability that the angular error is at most $\varepsilon$ when $s$ is uniform on the sphere and independent of $\omega\sim\rho$ and $x\sim P_T$.
--
--   Assume $L$ is admissible for the probability measure $\rho$, $d\ge3$ and $\varepsilon>0$, and let $a,q\in\mathbb N$ satisfy $2a\le d-1$, $q\ge2$ and $2q\le a$. Then
--
--   $$
--   \mathrm{Succ}(L,\rho,\varepsilon)\le(T+1)\cdot3\cdot4^{d}\,\varepsilon^{a}\cdot\bigl(32768^{d}\,(2^{M})^{1/q}\bigr)^{\lfloor T/q\rfloor+1}.
--   $$
--
--   The accuracy enters through $\varepsilon^{a}$, while the memory size enters only through the factor $(2^{M})^{(\lfloor T/q\rfloor+1)/q}$. With $q$ and $a$ chosen proportional to $d$, the right-hand side is below $2/3$ unless $T$ is large; together with the linear bound $T\ge d/4$, an elementary analysis of this tradeoff, for memory $M$ at most a constant times $d^2$, yields a sample lower bound of order $d\log(1/\varepsilon)$ for finite-state learners.
--
--   **Formalization Note** The learner is `L : Learner d M T Ω` with states `Fin (2^M)` and stop flags in `Bool` (`true` means stop); $\mathrm{Succ}(L,\rho,\varepsilon)$ is `L.uniformSuccess ρ ε`, valued in $[0,\infty]$, where $\sigma_d$ is `uniformSphere d` (the surface measure `volume.toSphere` divided by its total mass) and $P_T$ is `sampleLaw d T`; admissibility is `L.Admissible ρ`. The last factor is `streamFactor (E := Vector d) (J := State M) q ^ (T/q+1)`, i.e. $\bigl(32768^{\dim\mathbb R^d}\,|\mathcal Q|^{1/q}\bigr)^{\lfloor T/q\rfloor+1}$ with a real exponent $1/q$ and natural-number division `T/q`; the hypothesis $2a\le d-1$ uses truncated subtraction, which is harmless since $d\ge3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Success.lean#L71-L100

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

theorem OAI.NoiselessRegression.Learner.streaming_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    L.uniformSuccess ρ ε ≤
      (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) := by sorry
