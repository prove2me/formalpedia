-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_KernelLearner_uniformSuccess_asTape
-- name    : OAI.SubsphereCurrent.KernelLearner.uniformSuccess_asTape
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:47:58.193993+00:00
-- url     : https://prove2.me/theorems/43fffaa1-73a3-46ea-8ebd-988eab86fb78
-- title:
--   The random-tape realization of a randomized learner has the same uniform success probability
-- statement:
--   Fix $d,M,T\in\mathbb{N}$, let $Q=\{0,1,\dots,2^M-1\}$ be the set of memory states, let $S^{d-1}\subset\mathbb{R}^d$ be the Euclidean unit sphere, and let $\gamma_d$ be the standard Gaussian measure on $\mathbb{R}^d$. A *randomized learner* $L$ consists of an initial distribution $\pi_0$ on $\{\mathsf{go},\mathsf{stop}\}\times Q$, a transition distribution $K_t(q,o)$ on $\{\mathsf{go},\mathsf{stop}\}\times Q$ for every step $t\in\mathbb{N}$, state $q\in Q$ and observation $o\in\mathbb{R}^d\times\mathbb{R}$, and an output probability measure $O_{t,q}$ on $S^{d-1}$ for every $t\in\mathbb{N}$ and $q\in Q$. The learner has *Borel rules* if for every $t$, every $q$ and every $a\in\{\mathsf{go},\mathsf{stop}\}\times Q$ the map $o\mapsto K_t(q,o)(\{a\})$ is Borel measurable on $\mathbb{R}^d\times\mathbb{R}$.
--
--   Given a hidden unit vector $s\in S^{d-1}$ and samples $x=(x_1,\dots,x_T)\in(\mathbb{R}^d)^T$, the learner runs as a Markov chain whose status is either an active state $q\in Q$ or a stopped pair $(\tau,q)\in\mathbb{N}\times Q$: a draw $(b,q)\sim\pi_0$ gives the stopped pair $(0,q)$ if $b=\mathsf{stop}$ and the active state $q$ otherwise; at each step $t=1,\dots,T$ a stopped status is kept, while an active state $q$ draws $(b,q')\sim K_t\bigl(q,(x_t,\langle x_t,s\rangle)\bigr)$ and becomes $(t,q')$ if $b=\mathsf{stop}$ and $q'$ otherwise. The terminal pair is $(T,q)$ if the run is still active in state $q$ after step $T$, and the stopped pair otherwise. The estimate law $\mathrm{Est}_L(s,x)$ is the mixture of the measures $O_{\tau,q}$ weighted by the probabilities of the terminal pairs $(\tau,q)$, and the conditional success at accuracy $\varepsilon\in\mathbb{R}$ is the probability that the estimate lies within angle $\varepsilon$ of $s$:
--   $$
--   \mathrm{Succ}_L(\varepsilon;s,x)=\mathrm{Est}_L(s,x)\bigl(\{u\in S^{d-1}:\ \arccos\langle u,s\rangle\le\varepsilon\}\bigr).
--   $$
--
--   The *random tape* of $L$ is a triple $\omega=(a,r,\theta)$ consisting of an initial choice $a\in\{\mathsf{go},\mathsf{stop}\}\times Q$, coins $r=(r_1,\dots,r_T)\in\mathbb{R}^T$ and an output tape $\theta:\mathbb{N}\times Q\to S^{d-1}$, distributed according to the product measure
--   $$
--   \mu_L=\pi_0\otimes\lambda_{[0,1)}^{\otimes T}\otimes\bigotimes_{(t,q)\in\mathbb{N}\times Q}O_{t,q},
--   $$
--   where $\lambda_{[0,1)}$ is the uniform distribution on $[0,1)$. For a distribution $p$ on a finite set and a coin $u\in\mathbb{R}$, $\mathrm{Samp}(p,u)$ denotes inverse-CDF sampling: after fixing an enumeration $c_0,\dots,c_{m-1}$ of the set, it returns $c_i$ when $p(c_0)+\dots+p(c_{i-1})\le u<p(c_0)+\dots+p(c_i)$, and $c_0$ if there is no such $i$. The *tape realization* $L^{\mathrm{tape}}$ is the deterministic learner with randomness $\omega$ whose initial choice is $a$, whose transition at step $t$ from state $q$ on observation $o$ is $\mathrm{Samp}\bigl(K_t(q,o),r_t\bigr)$, and whose output at $(t,q)$ is the tape entry $\theta(t,q)$. On input $(s,\omega,x)$, with $s\in S^{d-1}$ and $x=(x_1,\dots,x_T)\in(\mathbb{R}^d)^T$, it starts in the stopped pair $(0,a_2)$ if the flag of $a=(a_1,a_2)$ is $\mathsf{stop}$ and in the active state $a_2$ otherwise; at each step $t=1,\dots,T$ a stopped status is kept, while an active state $q$ computes $(b,q')=\mathrm{Samp}\bigl(K_t(q,(x_t,\langle x_t,s\rangle)),r_t\bigr)$ and becomes the stopped pair $(t,q')$ if $b=\mathsf{stop}$ and the active state $q'$ otherwise. Its estimate is $\hat s(s,\omega,x)=\theta(\tau,q)$, where the terminal pair $(\tau,q)$ is $(T,q)$ if the run is still active in state $q$ after step $T$, and the stopped pair otherwise.
--
--   **Theorem.** Let $d\ge1$, let $L$ have Borel rules, let $\varepsilon\in\mathbb{R}$, and let $\bar\sigma_d$ be the normalized surface measure (uniform probability measure) on $S^{d-1}$. Then
--   $$
--   \bigl(\bar\sigma_d\otimes\mu_L\otimes\gamma_d^{\otimes T}\bigr)\Bigl(\bigl\{(s,\omega,x):\ \arccos\langle\hat s(s,\omega,x),s\rangle\le\varepsilon\bigr\}\Bigr)=\int_{S^{d-1}\times(\mathbb{R}^d)^T}\mathrm{Succ}_L(\varepsilon;s,x)\,d\bigl(\bar\sigma_d\otimes\gamma_d^{\otimes T}\bigr)(s,x).
--   $$
--
--   The left-hand side is the uniform success probability of the deterministic tape learner when the hidden vector is uniform on the sphere and the samples are independent standard Gaussian vectors; the right-hand side is the uniform success probability of the randomized learner itself. So passing to the tape realization loses nothing, and success guarantees for $L$ become success guarantees for a deterministic learner with an independent random seed.
--
--   **Formalization Note** The left-hand side is `L.asTape.uniformSuccess L.tapeLaw ε` and $\mathrm{Succ}_L$ is `L.conditionalSuccess`. The hypothesis $d\ge1$ is the instance `[NeZero d]`. In the tape realization the coin used at step $t$ is `tapeCoin t`, the coordinate $t-1$ of the coin vector when $t-1<T$ and $0$ otherwise, and the sampler is `samplePMF`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Kernels/Precision.lean#L766-L796

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

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.KernelLearner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u v w

theorem OAI.SubsphereCurrent.KernelLearner.uniformSuccess_asTape {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) (ε : ℝ) [NeZero d] :
    L.asTape.uniformSuccess L.tapeLaw ε =
      ∫⁻ z : UnitSphere d × Samples d T, L.conditionalSuccess ε z.1 z.2
        ∂(uniformSphere d).prod (sampleLaw d T) := by sorry
