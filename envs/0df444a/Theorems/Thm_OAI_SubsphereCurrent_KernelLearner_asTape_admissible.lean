-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_KernelLearner_asTape_admissible
-- name    : OAI.SubsphereCurrent.KernelLearner.asTape_admissible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:46:06.030076+00:00
-- url     : https://prove2.me/theorems/abc348d4-76e3-4092-984e-0227720b9941
-- title:
--   The random-tape realization of a randomized learner with Borel rules is admissible
-- statement:
--   Fix $d,M,T\in\mathbb{N}$, let $Q=\{0,1,\dots,2^M-1\}$ be the set of memory states, let $S^{d-1}\subset\mathbb{R}^d$ be the Euclidean unit sphere, and let $\gamma_d$ be the standard Gaussian measure on $\mathbb{R}^d$. A *randomized learner* $L$ consists of an initial distribution $\pi_0$ on $\{\mathsf{go},\mathsf{stop}\}\times Q$, a transition distribution $K_t(q,o)$ on $\{\mathsf{go},\mathsf{stop}\}\times Q$ for every step $t\in\mathbb{N}$, state $q\in Q$ and observation $o\in\mathbb{R}^d\times\mathbb{R}$, and an output probability measure $O_{t,q}$ on $S^{d-1}$ for every $t\in\mathbb{N}$ and $q\in Q$. The learner has *Borel rules* if for every $t$, every $q$ and every $a\in\{\mathsf{go},\mathsf{stop}\}\times Q$ the map $o\mapsto K_t(q,o)(\{a\})$ is Borel measurable on $\mathbb{R}^d\times\mathbb{R}$.
--
--   The *random tape* of $L$ is a triple $\omega=(a,r,\theta)$ consisting of an initial choice $a\in\{\mathsf{go},\mathsf{stop}\}\times Q$, coins $r=(r_1,\dots,r_T)\in\mathbb{R}^T$ and an output tape $\theta:\mathbb{N}\times Q\to S^{d-1}$, distributed according to the product measure
--   $$
--   \mu_L=\pi_0\otimes\lambda_{[0,1)}^{\otimes T}\otimes\bigotimes_{(t,q)\in\mathbb{N}\times Q}O_{t,q},
--   $$
--   where $\lambda_{[0,1)}$ is the uniform distribution on $[0,1)$. For a distribution $p$ on a finite set and a coin $u\in\mathbb{R}$, $\mathrm{Samp}(p,u)$ denotes inverse-CDF sampling: after fixing an enumeration $c_0,\dots,c_{m-1}$ of the set, it returns $c_i$ when $p(c_0)+\dots+p(c_{i-1})\le u<p(c_0)+\dots+p(c_i)$, and $c_0$ if there is no such $i$. The *tape realization* $L^{\mathrm{tape}}$ is the deterministic learner with randomness $\omega$ whose initial choice is $a$, whose transition at step $t$ from state $q$ on observation $o$ is $\mathrm{Samp}\bigl(K_t(q,o),r_t\bigr)$, and whose output at $(t,q)$ is the tape entry $\theta(t,q)$. On input $(s,\omega,x)$, with $s\in S^{d-1}$ and $x=(x_1,\dots,x_T)\in(\mathbb{R}^d)^T$, it starts in the stopped pair $(0,a_2)$ if the flag of $a=(a_1,a_2)$ is $\mathsf{stop}$ and in the active state $a_2$ otherwise; at each step $t=1,\dots,T$ a stopped status is kept, while an active state $q$ computes $(b,q')=\mathrm{Samp}\bigl(K_t(q,(x_t,\langle x_t,s\rangle)),r_t\bigr)$ and becomes the stopped pair $(t,q')$ if $b=\mathsf{stop}$ and the active state $q'$ otherwise. Its estimate is $\hat s(s,\omega,x)=\theta(\tau,q)$, where the terminal pair $(\tau,q)$ is $(T,q)$ if the run is still active in state $q$ after step $T$, and the stopped pair otherwise.
--
--   A deterministic learner whose randomness $\omega$ is distributed according to a measure $\mu$ is *admissible* for $\mu$ if:
--
--   1. the initial choice $\omega\mapsto a(\omega)$ is $\mu$-a.e. measurable;
--   2. for every step $t$ and state $q$, the transition $(\omega,o)\mapsto(\text{next value at step } t \text{ from } q)$ is a.e. measurable for $\mu\otimes(\gamma_d\otimes\lambda)$, where $\lambda$ is Lebesgue measure on $\mathbb{R}$;
--   3. for every $t$ and $q$, the output $\omega\mapsto(\text{output at } (t,q))$ is $\mu$-a.e. measurable;
--   4. for every $s\in S^{d-1}$, the map $(\omega,x)\mapsto\hat s(s,\omega,x)$ is a.e. measurable for $\mu\otimes\gamma_d^{\otimes T}$;
--   5. the map $(s,\omega,x)\mapsto\hat s(s,\omega,x)$ is a.e. measurable for $\bar\sigma_d\otimes\mu\otimes\gamma_d^{\otimes T}$, where $\bar\sigma_d$ is the normalized surface measure on $S^{d-1}$.
--
--   **Theorem.** If the randomized learner $L$ has Borel rules, then its tape realization $L^{\mathrm{tape}}$ is admissible for the tape law $\mu_L$.
--
--   Together with the equality of success probabilities between $L$ and $L^{\mathrm{tape}}$, this lets lower bounds proved for admissible deterministic learners driven by an auxiliary random seed be applied to randomized learners with Borel transition rules.
--
--   **Formalization Note** The statement is `L.asTape.Admissible L.tapeLaw`, where `Admissible` is the five-field structure of `SubsphereRegression.Learner`; the flag is a `Bool` with `true` meaning stop, and the states are `Fin (2^M)`. The coin used by the transition at step $t$ is `tapeCoin t`, the coordinate $t-1$ (truncated subtraction, so step $0$ would read the first coin) of the coin vector when $t-1<T$ and $0$ otherwise. The sampler is `samplePMF`, which transports `finiteSample` along `Fintype.equivFin`, and the output tape carries the infinite product measure `Measure.infinitePi`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Kernels/Precision.lean#L541-L554

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

theorem OAI.SubsphereCurrent.KernelLearner.asTape_admissible {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) : L.asTape.Admissible L.tapeLaw := by sorry
