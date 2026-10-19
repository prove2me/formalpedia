-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_Learner_streaming_success_bound_real
-- name    : OAI.SubsphereRegression.Learner.streaming_success_bound_real
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:39:21.923921+00:00
-- url     : https://prove2.me/theorems/86430a41-623a-4b4d-8a4e-415077710c40
-- title:
--   Real-number form of the streaming success bound at success probability $2/3$
-- statement:
--   **Setting.** Let $d,M,T\in\mathbb{N}$ and let $(\Omega,\rho)$ be a probability space of random seeds. Write $S^{d-1}\subset\mathbb{R}^d$ for the Euclidean unit sphere with its normalized surface measure $\sigma_d$, $\gamma_d$ for the standard Gaussian measure on $\mathbb{R}^d$, $\lambda$ for Lebesgue measure on $\mathbb{R}$, and $Q=\{0,1,\dots,2^M-1\}$ for the set of memory states (so the learner has $M$ bits of memory). A *seeded learner* $L$ consists of an initial choice $\iota:\Omega\to\{0,1\}\times Q$ (a stop flag and a state), transitions $\tau_t:\Omega\times Q\times(\mathbb{R}^d\times\mathbb{R})\to\{0,1\}\times Q$ and outputs $o_t:\Omega\times Q\to S^{d-1}$ for $t\in\mathbb{N}$. On a hidden vector $s\in S^{d-1}$, a seed $\omega$ and rows $x=(x_1,\dots,x_T)\in(\mathbb{R}^d)^T$, it starts with flag and state $\iota(\omega)$; while the flag is $0$, at times $t=1,\dots,T$ it reads the observation $(x_t,\langle x_t,s\rangle)$ and replaces its flag and state $q$ by $\tau_t(\omega,q,(x_t,\langle x_t,s\rangle))$. It stops at the first time $t^\ast\in\{0,\dots,T\}$ at which the flag is $1$ (time $0$ refers to the initial choice), or at $t^\ast=T$ if this never happens, in a state $q^\ast$, and returns the estimate $\hat s(s,\omega,x)=o_{t^\ast}(\omega,q^\ast)\in S^{d-1}$. For an accuracy $\varepsilon$, the success probability at a fixed $s$ and the uniform success probability are
--   $$\mathrm{succ}_\varepsilon(s)=(\rho\otimes\gamma_d^{\otimes T})\bigl\{(\omega,x):\arccos\langle\hat s(s,\omega,x),s\rangle\le\varepsilon\bigr\},$$
--   $$\mathrm{succ}_\varepsilon(\sigma_d)=(\sigma_d\otimes\rho\otimes\gamma_d^{\otimes T})\bigl\{(s,\omega,x):\arccos\langle\hat s(s,\omega,x),s\rangle\le\varepsilon\bigr\}.$$
--   The learner is *admissible* for $\rho$ if $\iota$ is $\rho$-a.e. measurable; for all $t$ and $q$ the map $(\omega,\xi)\mapsto\tau_t(\omega,q,\xi)$ is a.e. measurable for $\rho\otimes\gamma_d\otimes\lambda$ and $\omega\mapsto o_t(\omega,q)$ is $\rho$-a.e. measurable; for every fixed $s$ the map $(\omega,x)\mapsto\hat s(s,\omega,x)$ is a.e. measurable for $\rho\otimes\gamma_d^{\otimes T}$; and $(s,\omega,x)\mapsto\hat s(s,\omega,x)$ is a.e. measurable for $\sigma_d\otimes\rho\otimes\gamma_d^{\otimes T}$.
--
--   **Theorem.** Let $\rho$ be a probability measure and $L$ a seeded learner admissible for $\rho$. Let $d\ge3$, $\varepsilon>0$, and let $a,q\in\mathbb{N}$ satisfy $2a\le d-1$, $q\ge2$ and $2q\le a$. If $\mathrm{succ}_\varepsilon(\sigma_d)\ge2/3$, then, as an inequality between real numbers,
--
--   $$
--   \frac23\;\le\;(T+1)\,\bigl(3\cdot4^{d}\,\varepsilon^{a}\bigr)\,\Bigl(32768^{d}\,(2^{M})^{1/q}\Bigr)^{\lfloor T/q\rfloor+1}.
--   $$
--
--   This is the form consumed by the purely numerical argument which, after taking logarithms, extracts a lower bound on the number of samples $T$ of order $d\log(1/\varepsilon)$ for learners with $O(d^2)$ bits of memory.
--
--   **Formalization Note** The learner is `OAI.SubsphereRegression.Learner d M T Ω`; the hypothesis compares $2/3$ with the uniform success probability in $[0,\infty]$, while the conclusion is in $\mathbb{R}$. Here $\lfloor T/q\rfloor$ is natural-number division and $(2^M)^{1/q}$ is a real power.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Precision.lean#L163-L184

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

open OAI OAI.SubsphereRegression OAI.SubsphereRegression.Learner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
open scoped Pointwise

theorem OAI.SubsphereRegression.Learner.streaming_success_bound_real {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a)
    (hs : (2/3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε) :
    (2/3 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1) := by sorry
