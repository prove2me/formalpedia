-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_continuation_unroll
-- name    : OAI.SubsphereRegression.continuation_unroll
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:33:34.204389+00:00
-- url     : https://prove2.me/theorems/06b562b6-445d-481a-bdc5-d067c4bd7e7d
-- title:
--   Block unrolling of stream continuations over Gaussian rows
-- statement:
--   Let $E$ be a real inner product space of finite dimension with its Borel $\sigma$-algebra and standard Gaussian measure $\gamma_E$, and let $J$ be a finite set carrying a $\sigma$-algebra in which singletons are measurable. Let $\delta=(\delta_t)_{t\in\mathbb{N}}$, $\delta_t:J\times(E\times\mathbb{R})\to J$, be a transition rule, and for $n,k\in\mathbb{N}$ and $j\in J$ let the *route* $R_{n,k}(j;\cdot):E^k\times\mathbb{R}^k\to J$ send $(A,b)$ to the state $j_k$ obtained from $j_0=j$ by $j_i=\delta_{n+i}(j_{i-1},(A_i,b_i))$, $i=1,\dots,k$. Given arbitrary weights $w_t:J\times E\to[0,\infty]$ ($t\in\mathbb{N}$), the *continuation* $V_{n,k}(j,s)$ is defined by recursion on $k$:
--
--   $$
--   V_{n,0}(j,s)=w_n(j,s),\qquad V_{n,k+1}(j,s)=\int_E V_{n+1,k}\bigl(\delta_{n+1}(j,(x,\langle s,x\rangle)),\,s\bigr)\,d\gamma_E(x).
--   $$
--
--   Thus $V_{n,k}(j,s)$ is the expected terminal weight when a stream started in state $j$ at time $n$ reads, one at a time, $k$ independent Gaussian rows labelled by their inner products with a hidden vector $s$.
--
--   **Theorem.** If each map $\delta_t(j,\cdot):E\times\mathbb{R}\to J$ is measurable, then for all $n,m,k\in\mathbb{N}$, $j\in J$ and $s\in E$,
--
--   $$
--   V_{n,m+k}(j,s)=\int_{E^m}V_{n+m,k}\Bigl(R_{n,m}\bigl(j;\,A,(\langle s,A_i\rangle)_{i=1}^m\bigr),\,s\Bigr)\,d\gamma_E^{\otimes m}(A).
--   $$
--
--   In words, the first $m$ steps can be processed as one block: draw all $m$ rows at once, move to the state reached after the block, and continue from there. This converts the step-by-step recursion into block form, so that estimates for a single block of rows (such as routing bounds) can be iterated along a long stream.
--
--   **Formalization Note** The continuation is `continuation δ w n k j s`, and the right-hand side is `blockValue (fun a => continuation δ w (n+m) k a) (streamRoute δ n m j) s`, where `blockValue h φ s` denotes $\int_{E^m}h\bigl(\varphi(A,(\langle s,A_i\rangle)_i)\bigr)(s)\,d\gamma_E^{\otimes m}(A)$. Integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions; no measurability of the weights $w_t$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Streaming.lean#L86-L110

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
open scoped Topology
open InnerProductSpace
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

theorem OAI.SubsphereRegression.continuation_unroll {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j))
    (n m k : ℕ) (j : J) (s : E) :
    continuation δ w n (m+k) j s =
      blockValue (fun a => continuation δ w (n+m) k a) (streamRoute δ n m j) s := by sorry
