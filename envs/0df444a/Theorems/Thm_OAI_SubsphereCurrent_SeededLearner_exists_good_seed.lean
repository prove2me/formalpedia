-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_SeededLearner_exists_good_seed
-- name    : OAI.SubsphereCurrent.SeededLearner.exists_good_seed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:48:37.912888+00:00
-- url     : https://prove2.me/theorems/9c380ce3-53f4-474f-807a-4dd84a2997fc
-- title:
--   Some seed of a seeded learner succeeds at least as well as the seed average
-- statement:
--   Fix $d,M,T\in\mathbb{N}$, let $Q=\{0,1,\dots,2^M-1\}$ be the set of memory states, let $S^{d-1}\subset\mathbb{R}^d$ be the Euclidean unit sphere, and let $\gamma_d$ be the standard Gaussian measure on $\mathbb{R}^d$. A *randomized learner* $L$ consists of an initial distribution $\pi_0$ on $\{\mathsf{go},\mathsf{stop}\}\times Q$, a transition distribution $K_t(q,o)$ on $\{\mathsf{go},\mathsf{stop}\}\times Q$ for every step $t\in\mathbb{N}$, state $q\in Q$ and observation $o\in\mathbb{R}^d\times\mathbb{R}$, and an output probability measure $O_{t,q}$ on $S^{d-1}$ for every $t\in\mathbb{N}$ and $q\in Q$.
--
--   Given a hidden unit vector $s\in S^{d-1}$ and samples $x=(x_1,\dots,x_T)\in(\mathbb{R}^d)^T$, the learner runs as a Markov chain whose status is either an active state $q\in Q$ or a stopped pair $(\tau,q)\in\mathbb{N}\times Q$: a draw $(b,q)\sim\pi_0$ gives the stopped pair $(0,q)$ if $b=\mathsf{stop}$ and the active state $q$ otherwise; at each step $t=1,\dots,T$ a stopped status is kept, while an active state $q$ draws $(b,q')\sim K_t\bigl(q,(x_t,\langle x_t,s\rangle)\bigr)$ and becomes $(t,q')$ if $b=\mathsf{stop}$ and $q'$ otherwise. The terminal pair is $(T,q)$ if the run is still active in state $q$ after step $T$, and the stopped pair otherwise. The estimate law $\mathrm{Est}_L(s,x)$ is the mixture of the measures $O_{\tau,q}$ weighted by the probabilities of the terminal pairs $(\tau,q)$, and the conditional success at accuracy $\varepsilon\in\mathbb{R}$ is the probability that the estimate lies within angle $\varepsilon$ of $s$:
--   $$
--   \mathrm{Succ}_L(\varepsilon;s,x)=\mathrm{Est}_L(s,x)\bigl(\{u\in S^{d-1}:\ \arccos\langle u,s\rangle\le\varepsilon\}\bigr).
--   $$
--
--   Let $\lambda$ be Lebesgue measure on $\mathbb{R}$ and $\bar\sigma_d$ the normalized surface measure on $S^{d-1}$. The learner has *completed rules* if for every $t$, $q$ and $a\in\{\mathsf{go},\mathsf{stop}\}\times Q$ the map $o\mapsto K_t(q,o)(\{a\})$ is a.e. measurable for $\gamma_d\otimes\lambda$. A *seeded learner* over a measurable space $\Omega$ is a family $(L_\omega)_{\omega\in\Omega}$ of randomized learners with the same $d,M,T$. For a probability measure $\rho$ on $\Omega$ it is *admissible* if (i) $L_\omega$ has completed rules for $\rho$-almost every $\omega$; (ii) for every $s\in S^{d-1}$ and $\varepsilon\in\mathbb{R}$, the map $(\omega,x)\mapsto\mathrm{Succ}_{L_\omega}(\varepsilon;s,x)$ is a.e. measurable for $\rho\otimes\gamma_d^{\otimes T}$; and (iii) for every $\varepsilon$, the map $(s,\omega,x)\mapsto\mathrm{Succ}_{L_\omega}(\varepsilon;s,x)$ is a.e. measurable for $\bar\sigma_d\otimes\rho\otimes\gamma_d^{\otimes T}$. Its uniform success is
--   $$
--   U_\rho(\varepsilon)=\int\mathrm{Succ}_{L_\omega}(\varepsilon;s,x)\,d\bigl(\bar\sigma_d\otimes\rho\otimes\gamma_d^{\otimes T}\bigr)(s,\omega,x).
--   $$
--
--   **Theorem.** Let $d\ge1$, let $\rho$ be a probability measure on $\Omega$, let $(L_\omega)$ be a seeded learner admissible for $\rho$, and let $\varepsilon\in\mathbb{R}$. Then there exists a seed $\omega\in\Omega$ such that $L_\omega$ has completed rules and
--   $$
--   U_\rho(\varepsilon)\le\int_{S^{d-1}\times(\mathbb{R}^d)^T}\mathrm{Succ}_{L_\omega}(\varepsilon;s,x)\,d\bigl(\bar\sigma_d\otimes\gamma_d^{\otimes T}\bigr)(s,x).
--   $$
--
--   This is the averaging step that removes the shared seed: any lower bound on the uniform success of a seeded learner is inherited by a single randomized learner with completed rules, to which the analysis of one fixed learner applies.
--
--   **Formalization Note** The seeded learner is `SeededLearner d M T Ω` with field `rules`, admissibility is `SeededLearner.Admissible`, and completed rules are `KernelLearner.CompletedRules`, stated with respect to `observationReference d` (standard Gaussian on $\mathbb{R}^d$ times Lebesgue measure on $\mathbb{R}$). The hypothesis $d\ge1$ is the instance `[NeZero d]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Kernels/Precision.lean#L830-L854

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

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.SeededLearner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u v w

theorem OAI.SubsphereCurrent.SeededLearner.exists_good_seed {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (ε : ℝ) [NeZero d] :
    ∃ ω, (L.rules ω).CompletedRules ∧ L.uniformSuccess ρ ε ≤
      ∫⁻ z : UnitSphere d × Samples d T, (L.rules ω).conditionalSuccess ε z.1 z.2
        ∂(uniformSphere d).prod (sampleLaw d T) := by sorry
