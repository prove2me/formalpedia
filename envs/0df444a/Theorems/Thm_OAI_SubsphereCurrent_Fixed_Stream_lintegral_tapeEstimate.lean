-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_Fixed_Stream_lintegral_tapeEstimate
-- name    : OAI.SubsphereCurrent.Fixed.Stream.lintegral_tapeEstimate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:56:35.717791+00:00
-- url     : https://prove2.me/theorems/c6b3c2c8-9bdb-4ad4-8957-121ce3f36ce4
-- title:
--   Random-tape representation of the output law of a finite-state stream
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $J$ be a finite nonempty set of states carrying a $\sigma$-algebra in which singletons are measurable, and let $T\in\mathbb{N}$. A *finite-state stream* $L$ on $E$ with states $J$ and horizon $T$ consists of an initial distribution $\pi_0$ on $J$, transition distributions $K_t(q,o)$ on $J$ for $t\in\mathbb{N}$, $q\in J$ and observations $o\in E\times\mathbb{R}$, and output probability measures $O_q$ on $E$ for $q\in J$. For $s\in E$ and $x=(x_1,\dots,x_T)\in E^T$ its run is the Markov chain $q_0\sim\pi_0$, $q_t\sim K_t\bigl(q_{t-1},(x_t,\langle x_t,s\rangle)\bigr)$ for $t=1,\dots,T$, and its estimate law $\mathrm{Est}_L(s,x)=\sum_{j\in J}\Pr[q_T=j]\,O_j$ is the law of an output drawn from $O_{q_T}$. The stream has *Borel rules* if $o\mapsto K_t(q,o)(\{a\})$ is measurable for all $t$, $q$ and $a$.
--
--   The *random tape* of $L$ is a triple $\omega=(q,r,\theta)$ with $q\in J$, coins $r=(r_1,\dots,r_T)\in\mathbb{R}^T$ and a table $\theta\in E^J$ of pre-drawn outputs, distributed according to
--   $$
--   \mu_L=\pi_0\otimes\lambda_{[0,1)}^{\otimes T}\otimes\bigotimes_{j\in J}O_j ,
--   $$
--   where $\lambda_{[0,1)}$ is the uniform distribution on $[0,1)$. For a distribution $p$ on $J$ and $u\in\mathbb{R}$, $\mathrm{Samp}(p,u)$ is inverse-CDF sampling: after fixing an enumeration $j_0,\dots,j_{m-1}$ of $J$, it returns $j_i$ when $p(j_0)+\dots+p(j_{i-1})\le u<p(j_0)+\dots+p(j_i)$, and $j_0$ if there is no such $i$. The *tape estimate* $\hat s(s,\omega,x)$ runs the chain deterministically, $q_0=q$ and $q_t=\mathrm{Samp}\bigl(K_t(q_{t-1},(x_t,\langle x_t,s\rangle)),r_t\bigr)$ for $t=1,\dots,T$, and outputs the table entry $\theta(q_T)$.
--
--   **Theorem.** If $L$ has Borel rules, then for all $s\in E$, all $x\in E^T$ and every measurable $f:E\to[0,\infty]$,
--   $$
--   \int f\bigl(\hat s(s,\omega,x)\bigr)\,d\mu_L(\omega)=\int_E f\,d\,\mathrm{Est}_L(s,x).
--   $$
--
--   Equivalently, under $\mu_L$ the tape estimate has law $\mathrm{Est}_L(s,x)$: all the randomness of the stream can be moved into an independent tape of an initial state, uniform coins and pre-drawn outputs, after which the stream is a deterministic function of its input. This allows a randomized stream to be analysed with arguments for deterministic procedures that use an auxiliary random seed.
--
--   **Formalization Note** The stream is `Fixed.Stream E J T`, the tape law is `L.tapeLaw`, the tape estimate is `L.tapeEstimate s ω x` (computed with `detChain` and the sampler `samplePMF`), and $\mathrm{Est}_L$ is `L.estimateLaw s x`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Geometry/Affine.lean#L121-L147

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
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine

open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Fixed OAI.SubsphereCurrent.Fixed.Stream
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J] [Nonempty J]
  {T : ℕ}

theorem OAI.SubsphereCurrent.Fixed.Stream.lintegral_tapeEstimate (L : Stream E J T) (hL : L.BorelRules)
    (s : E) (x : Fin T → E) (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (L.tapeEstimate s ω x) ∂L.tapeLaw) = ∫⁻ u, f u ∂L.estimateLaw s x := by sorry
