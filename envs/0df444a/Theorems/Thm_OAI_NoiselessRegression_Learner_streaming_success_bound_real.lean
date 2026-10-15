-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_Learner_streaming_success_bound_real
-- name    : OAI.NoiselessRegression.Learner.streaming_success_bound_real
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T09:49:14.764076+00:00
-- url     : https://prove2.me/theorems/d2d32a85-255f-4e61-8848-cbaf8c525ae2
-- title:
--   A $2^M$-state learner with uniform-prior success at least $2/3$ satisfies an explicit real inequality
-- statement:
--   Fix $d,M,T\in\mathbb N$. Write $S^{d-1}=\{u\in\mathbb R^d:\|u\|=1\}$ for the Euclidean unit sphere, $\langle\cdot,\cdot\rangle$ for the standard inner product, and $\mathcal Q=\{0,1,\dots,2^M-1\}$ for the set of $2^M$ memory states. Let $(\Omega,\mathcal F)$ be a measurable space of internal randomness. A *learner* $L$ consists of an initial choice $\iota:\Omega\to\{\mathrm{stop},\mathrm{go}\}\times\mathcal Q$, transitions $\tau_t:\Omega\times\mathcal Q\times(\mathbb R^d\times\mathbb R)\to\{\mathrm{stop},\mathrm{go}\}\times\mathcal Q$ and outputs $o_t:\Omega\times\mathcal Q\to S^{d-1}$ for $t\in\mathbb N$. Given an unknown $s\in S^{d-1}$, randomness $\omega\in\Omega$ and samples $x=(x_1,\dots,x_T)\in(\mathbb R^d)^T$, the learner starts in the state $b_0$ given by $\iota(\omega)$ and stops at time $0$ if $\iota(\omega)$ says stop. At each step $t=1,\dots,T$ at which it has not stopped, it reads the row $x_t$ with its noiseless label $\langle x_t,s\rangle$, and $\tau_t\bigl(\omega,b_{t-1},(x_t,\langle x_t,s\rangle)\bigr)$ gives the new state $b_t$ and decides whether to stop at time $t$. If it never stops, the run ends at time $T$. If $t^{\ast}$ is the stopping time and $b_{t^{\ast}}$ the state at that time, the estimate is $\hat s_L(s,\omega,x)=o_{t^{\ast}}(\omega,b_{t^{\ast}})\in S^{d-1}$, and its angular error is $\arccos\langle\hat s_L(s,\omega,x),s\rangle$.
--
--   Let $\sigma_d$ be the uniform probability measure on $S^{d-1}$ (normalized surface measure), $\gamma_d$ the standard Gaussian measure on $\mathbb R^d$, $P_T=\gamma_d^{\otimes T}$ the law of $T$ independent standard Gaussian rows, $\lambda$ Lebesgue measure on $\mathbb R$, and $\rho$ a probability measure on $\Omega$. The learner is *admissible* for $\rho$ if $\iota$ is $\rho$-a.e. measurable; for every $t$ and $b\in\mathcal Q$ the map $(\omega,(x,y))\mapsto\tau_t(\omega,b,(x,y))$ is a.e. measurable for $\rho\otimes(\gamma_d\otimes\lambda)$ and $o_t(\cdot,b)$ is $\rho$-a.e. measurable; for every $s$ the map $(\omega,x)\mapsto\hat s_L(s,\omega,x)$ is $\rho\otimes P_T$-a.e. measurable; and $(s,\omega,x)\mapsto\hat s_L(s,\omega,x)$ is $\sigma_d\otimes\rho\otimes P_T$-a.e. measurable. For $\varepsilon\in\mathbb R$ the *uniform-prior success probability* is $\mathrm{Succ}(L,\rho,\varepsilon)=(\sigma_d\otimes\rho\otimes P_T)\bigl\{(s,\omega,x):\arccos\langle\hat s_L(s,\omega,x),s\rangle\le\varepsilon\bigr\}$, the probability that the angular error is at most $\varepsilon$ when $s$ is uniform on the sphere and independent of $\omega\sim\rho$ and $x\sim P_T$.
--
--   Assume $L$ is admissible for the probability measure $\rho$, $d\ge3$ and $\varepsilon>0$, let $a,q\in\mathbb N$ satisfy $2a\le d-1$, $q\ge2$ and $2q\le a$, and assume $\mathrm{Succ}(L,\rho,\varepsilon)\ge2/3$. Then, as an inequality between real numbers,
--
--   $$
--   \frac23\le(T+1)\bigl(3\cdot4^{d}\,\varepsilon^{a}\bigr)\bigl(32768^{d}\,(2^{M})^{1/q}\bigr)^{\lfloor T/q\rfloor+1}.
--   $$
--
--   This is the real-valued form of the uniform-prior success bound for learners with $2^M$ memory states, ready for taking logarithms. Combined with the linear bound $T\ge d/4$ and an elementary estimate (with $q$ and $a$ proportional to $d$), it yields the sample lower bound $T\ge c\,d\log(1/\varepsilon)$ for learners with at most $A\,d^2$ bits of memory.
--
--   **Formalization Note** The learner is `L : Learner d M T Ω` with states `Fin (2^M)` and stop flags in `Bool` (`true` means stop); $\mathrm{Succ}(L,\rho,\varepsilon)$ is `L.uniformSuccess ρ ε`, valued in $[0,\infty]$, where $\sigma_d$ is `uniformSphere d` (the surface measure `volume.toSphere` divided by its total mass) and $P_T$ is `sampleLaw d T`; admissibility is `L.Admissible ρ`. The hypothesis is `(2/3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε`; in the conclusion $(2^M)^{1/q}$ is the real power `((2:ℝ)^M)^(1/(q:ℝ))` and $\lfloor T/q\rfloor$ is the natural-number division `T/q`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Precision.lean#L22-L43

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

theorem OAI.NoiselessRegression.Learner.streaming_success_bound_real {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a)
    (hs : (2/3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε) :
    (2/3 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1) := by sorry
