-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_KernelLearner_borelVersion_success_ae
-- name    : OAI.SubsphereCurrent.KernelLearner.borelVersion_success_ae
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:41:20.546039+00:00
-- url     : https://prove2.me/theorems/5820ec48-01a4-48f3-a71e-ebb45a659ca6
-- title:
--   Borel versions of almost-everywhere measurable transition kernels preserve conditional success almost everywhere
-- statement:
--   **Setting.** Fix $d,M,T\in\mathbb{N}$. Let $S^{d-1}$ be the unit sphere of $\mathbb{R}^d$ with its normalized surface measure $\sigma_d$, $\gamma_d$ the standard Gaussian measure on $\mathbb{R}^d$, $\lambda$ Lebesgue measure on $\mathbb{R}$, and $Q=\{0,\dots,2^M-1\}$ the set of memory states. A *kernel learner* $L$ consists of an initial distribution $\pi_0$ on $\{0,1\}\times Q$ (a stop flag and a state), transition kernels assigning to each time $t\in\mathbb{N}$, state $q$ and observation $\xi\in\mathbb{R}^d\times\mathbb{R}$ a probability distribution $\tau_t(q,\xi)$ on $\{0,1\}\times Q$, and output probability measures $o_t(q)$ on $S^{d-1}$. On a hidden vector $s\in S^{d-1}$ and rows $x\in(\mathbb{R}^d)^T$ it runs as a Markov chain: it draws its flag and state from $\pi_0$; while the flag is $0$, at times $t=1,\dots,T$ it draws a new flag and state from $\tau_t(q,(x_t,\langle x_t,s\rangle))$; it stops at the first time $t^\ast$ at which the flag is $1$ (time $0$ refers to the initial draw), or at $t^\ast=T$, in a state $q^\ast$, and then draws its estimate $u$ from $o_{t^\ast}(q^\ast)$. The *conditional success* $\mathrm{cs}^L_\varepsilon(s,x)$ is the probability that $\arccos\langle u,s\rangle\le\varepsilon$. The learner has *completed rules* if for all $t$, $q$ and every outcome $e\in\{0,1\}\times Q$ the function $\xi\mapsto\tau_t(q,\xi)(e)$ is a.e. measurable for $\gamma_d\otimes\lambda$.
--
--   For such $L$, its *Borel version* $L^{\mathrm B}$ has the same initial distribution and outputs, and transition kernels built as follows: for every $t,q,e$ fix a measurable function $p_{t,q,e}$ that equals $\xi\mapsto\tau_t(q,\xi)(e)$ outside a $(\gamma_d\otimes\lambda)$-null set; at observations $\xi$ with $\sum_ep_{t,q,e}(\xi)=1$ the new kernel is the distribution with weights $p_{t,q,e}(\xi)$, and at all other $\xi$ it is a point mass at a fixed outcome.
--
--   **Theorem.** If $L$ has completed rules and $d\ge3$, then for every real $\varepsilon$,
--
--   $$
--   \mathrm{cs}^{L}_\varepsilon(s,x)=\mathrm{cs}^{L^{\mathrm B}}_\varepsilon(s,x)\qquad\text{for }(\sigma_d\otimes\gamma_d^{\otimes T})\text{-almost every }(s,x)\in S^{d-1}\times(\mathbb{R}^d)^T.
--   $$
--
--   The Borel version has genuinely measurable transition probabilities, as required by the estimates for streaming learners, while its conditional success agrees almost everywhere with that of the original learner; in particular every integral of the conditional success against $\sigma_d\otimes\gamma_d^{\otimes T}$ is unchanged. This lets lower bounds proved for learners with Borel rules be transferred to learners whose rules are only measurable up to null sets.
--
--   **Formalization Note** The learner is `OAI.SubsphereCurrent.KernelLearner d M T`, with `PMF`-valued initial and transition laws; the measurable representatives are chosen with `AEMeasurable.mk`, the fallback point mass sits at `Classical.arbitrary`, and the Borel version `L.borelVersion hL` depends on the proof `hL` of completed rules.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Kernels/Precision.lean#L85-L102

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

theorem OAI.SubsphereCurrent.KernelLearner.borelVersion_success_ae {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.CompletedRules) (hd : 3 ≤ d) (ε : ℝ) :
    (fun z : UnitSphere d × Samples d T => L.conditionalSuccess ε z.1 z.2) =ᵐ[
      (uniformSphere d).prod (sampleLaw d T)]
    (fun z => (L.borelVersion hL).conditionalSuccess ε z.1 z.2) := by sorry
