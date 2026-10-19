-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_Learner_streaming_success_bound
-- name    : OAI.SubsphereRegression.Learner.streaming_success_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:37:55.979984+00:00
-- url     : https://prove2.me/theorems/31fc8b9d-9faa-4353-9d4c-d29ae713dc5a
-- title:
--   Uniform success bound for seeded finite-memory learners of a hidden unit vector
-- statement:
--   **Setting.** Let $d,M,T\in\mathbb{N}$ and let $(\Omega,\rho)$ be a probability space of random seeds. Write $S^{d-1}\subset\mathbb{R}^d$ for the Euclidean unit sphere with its normalized surface measure $\sigma_d$, $\gamma_d$ for the standard Gaussian measure on $\mathbb{R}^d$, $\lambda$ for Lebesgue measure on $\mathbb{R}$, and $Q=\{0,1,\dots,2^M-1\}$ for the set of memory states (so the learner has $M$ bits of memory). A *seeded learner* $L$ consists of an initial choice $\iota:\Omega\to\{0,1\}\times Q$ (a stop flag and a state), transitions $\tau_t:\Omega\times Q\times(\mathbb{R}^d\times\mathbb{R})\to\{0,1\}\times Q$ and outputs $o_t:\Omega\times Q\to S^{d-1}$ for $t\in\mathbb{N}$. On a hidden vector $s\in S^{d-1}$, a seed $\omega$ and rows $x=(x_1,\dots,x_T)\in(\mathbb{R}^d)^T$, it starts with flag and state $\iota(\omega)$; while the flag is $0$, at times $t=1,\dots,T$ it reads the observation $(x_t,\langle x_t,s\rangle)$ and replaces its flag and state $q$ by $\tau_t(\omega,q,(x_t,\langle x_t,s\rangle))$. It stops at the first time $t^\ast\in\{0,\dots,T\}$ at which the flag is $1$ (time $0$ refers to the initial choice), or at $t^\ast=T$ if this never happens, in a state $q^\ast$, and returns the estimate $\hat s(s,\omega,x)=o_{t^\ast}(\omega,q^\ast)\in S^{d-1}$. For an accuracy $\varepsilon$, the success probability at a fixed $s$ and the uniform success probability are
--   $$\mathrm{succ}_\varepsilon(s)=(\rho\otimes\gamma_d^{\otimes T})\bigl\{(\omega,x):\arccos\langle\hat s(s,\omega,x),s\rangle\le\varepsilon\bigr\},$$
--   $$\mathrm{succ}_\varepsilon(\sigma_d)=(\sigma_d\otimes\rho\otimes\gamma_d^{\otimes T})\bigl\{(s,\omega,x):\arccos\langle\hat s(s,\omega,x),s\rangle\le\varepsilon\bigr\}.$$
--   The learner is *admissible* for $\rho$ if $\iota$ is $\rho$-a.e. measurable; for all $t$ and $q$ the map $(\omega,\xi)\mapsto\tau_t(\omega,q,\xi)$ is a.e. measurable for $\rho\otimes\gamma_d\otimes\lambda$ and $\omega\mapsto o_t(\omega,q)$ is $\rho$-a.e. measurable; for every fixed $s$ the map $(\omega,x)\mapsto\hat s(s,\omega,x)$ is a.e. measurable for $\rho\otimes\gamma_d^{\otimes T}$; and $(s,\omega,x)\mapsto\hat s(s,\omega,x)$ is a.e. measurable for $\sigma_d\otimes\rho\otimes\gamma_d^{\otimes T}$.
--
--   **Theorem.** Let $\rho$ be a probability measure and $L$ a seeded learner admissible for $\rho$. Let $d\ge3$, $\varepsilon>0$, and let $a,q\in\mathbb{N}$ satisfy $2a\le d-1$, $q\ge2$ and $2q\le a$. Then
--
--   $$
--   \mathrm{succ}_\varepsilon(\sigma_d)\;\le\;(T+1)\cdot3\cdot4^{d}\,\varepsilon^{a}\cdot\Bigl(32768^{d}\,(2^{M})^{1/q}\Bigr)^{\lfloor T/q\rfloor+1}.
--   $$
--
--   The right-hand side decays like $\varepsilon^a$ with $a$ of order $d$, while the memory enters only through $(2^M)^{1/q}$ per block of $q$ samples. Taking logarithms in this inequality is how the explicit lower bound $T\ge c\,d\log(1/\varepsilon)$ for learners with $O(d^2)$ bits of memory is obtained.
--
--   **Formalization Note** The learner is `OAI.SubsphereRegression.Learner d M T Ω`, with `Bool` stop flags and states `Fin (2^M)`; the seed measure is a probability measure by an instance argument. Probabilities are extended nonnegative reals, $\lfloor T/q\rfloor$ is natural-number division, and the factor $32768^d(2^M)^{1/q}$ appears as `streamFactor q` for the state type, whose cardinality is $2^M$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Precision.lean#L128-L157

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

theorem OAI.SubsphereRegression.Learner.streaming_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    L.uniformSuccess ρ ε ≤
      (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) := by sorry
