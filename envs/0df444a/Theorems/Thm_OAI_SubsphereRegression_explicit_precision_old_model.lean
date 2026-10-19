-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_explicit_precision_old_model
-- name    : OAI.SubsphereRegression.explicit_precision_old_model
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:40:42.925949+00:00
-- url     : https://prove2.me/theorems/25e63e5e-76c9-47f7-bed7-9f2aa0516ae2
-- title:
--   Sample lower bound $T\ge2^{-16}d\log_2(1/\varepsilon)$ for seeded learners with $o(d^2)$ bits of memory
-- statement:
--   **Setting.** Let $d,M,T\in\mathbb{N}$ and let $(\Omega,\rho)$ be a probability space of random seeds. Write $S^{d-1}\subset\mathbb{R}^d$ for the Euclidean unit sphere with its normalized surface measure $\sigma_d$, $\gamma_d$ for the standard Gaussian measure on $\mathbb{R}^d$, $\lambda$ for Lebesgue measure on $\mathbb{R}$, and $Q=\{0,1,\dots,2^M-1\}$ for the set of memory states (so the learner has $M$ bits of memory). A *seeded learner* $L$ consists of an initial choice $\iota:\Omega\to\{0,1\}\times Q$ (a stop flag and a state), transitions $\tau_t:\Omega\times Q\times(\mathbb{R}^d\times\mathbb{R})\to\{0,1\}\times Q$ and outputs $o_t:\Omega\times Q\to S^{d-1}$ for $t\in\mathbb{N}$. On a hidden vector $s\in S^{d-1}$, a seed $\omega$ and rows $x=(x_1,\dots,x_T)\in(\mathbb{R}^d)^T$, it starts with flag and state $\iota(\omega)$; while the flag is $0$, at times $t=1,\dots,T$ it reads the observation $(x_t,\langle x_t,s\rangle)$ and replaces its flag and state $q$ by $\tau_t(\omega,q,(x_t,\langle x_t,s\rangle))$. It stops at the first time $t^\ast\in\{0,\dots,T\}$ at which the flag is $1$ (time $0$ refers to the initial choice), or at $t^\ast=T$ if this never happens, in a state $q^\ast$, and returns the estimate $\hat s(s,\omega,x)=o_{t^\ast}(\omega,q^\ast)\in S^{d-1}$. For an accuracy $\varepsilon$, the success probability at a fixed $s$ and the uniform success probability are
--   $$\mathrm{succ}_\varepsilon(s)=(\rho\otimes\gamma_d^{\otimes T})\bigl\{(\omega,x):\arccos\langle\hat s(s,\omega,x),s\rangle\le\varepsilon\bigr\},$$
--   $$\mathrm{succ}_\varepsilon(\sigma_d)=(\sigma_d\otimes\rho\otimes\gamma_d^{\otimes T})\bigl\{(s,\omega,x):\arccos\langle\hat s(s,\omega,x),s\rangle\le\varepsilon\bigr\}.$$
--   The learner is *admissible* for $\rho$ if $\iota$ is $\rho$-a.e. measurable; for all $t$ and $q$ the map $(\omega,\xi)\mapsto\tau_t(\omega,q,\xi)$ is a.e. measurable for $\rho\otimes\gamma_d\otimes\lambda$ and $\omega\mapsto o_t(\omega,q)$ is $\rho$-a.e. measurable; for every fixed $s$ the map $(\omega,x)\mapsto\hat s(s,\omega,x)$ is a.e. measurable for $\rho\otimes\gamma_d^{\otimes T}$; and $(s,\omega,x)\mapsto\hat s(s,\omega,x)$ is a.e. measurable for $\sigma_d\otimes\rho\otimes\gamma_d^{\otimes T}$.
--
--   **Theorem.** Let $M:\mathbb{N}\to\mathbb{N}$ satisfy $M(d)=o(d^2)$ as $d\to\infty$. Then there is $d_0\in\mathbb{N}$ such that the following holds for every $d\ge d_0$, every $T\in\mathbb{N}$, every $\varepsilon$ with $0<\varepsilon\le1/10$, every probability space $(\Omega,\rho)$, and every seeded learner $L$ with $2^{M(d)}$ memory states that is admissible for $\rho$: if $\mathrm{succ}_\varepsilon(\sigma_d)\ge2/3$, or $\mathrm{succ}_\varepsilon(s)\ge2/3$ for every $s\in S^{d-1}$, then
--
--   $$
--   2^{-16}\,d\,\log_2\frac1\varepsilon\;\le\;T.
--   $$
--
--   So a one-pass learner with subquadratic memory that recovers a hidden unit vector to angular accuracy $\varepsilon$ from noiseless Gaussian linear measurements, with probability $2/3$, must read at least $2^{-16}d\log_2(1/\varepsilon)$ samples. The constant $2^{-16}$ is absolute; only the threshold $d_0$ depends on the memory function $M$. The learners here have transitions that are deterministic given the seed; the bound has the same form as the explicit-precision bound for learners with randomized transition kernels.
--
--   **Formalization Note** The learner is `OAI.SubsphereRegression.Learner d (M d) T Ω`, with seeds in an arbitrary type `Ω` of a fixed universe; $M(d)=o(d^2)$ is `Asymptotics.IsLittleO atTop` of the real sequences $M(d)$ and $d^2$. Success probabilities are extended nonnegative reals and $\log_2$ is `Real.logb 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Estimates/Numerics.lean#L108-L155

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

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u

theorem OAI.SubsphereRegression.explicit_precision_old_model :
  ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ) ^ 2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Learner d (M d) T Ω, L.Admissible ρ →
    ((2 / 3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε ∨
      ∀ s, (2 / 3 : ℝ≥0∞) ≤ L.success ρ ε s) →
    (2 : ℝ)⁻¹ ^ 16 * (d : ℝ) * Real.logb 2 (1 / ε) ≤ (T : ℝ) := by sorry
