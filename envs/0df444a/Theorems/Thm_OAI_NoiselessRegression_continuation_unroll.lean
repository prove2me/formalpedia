-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_continuation_unroll
-- name    : OAI.NoiselessRegression.continuation_unroll
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:38:53.044978+00:00
-- url     : https://prove2.me/theorems/c5e85e39-e5c9-46ae-b133-56d3a16d485f
-- title:
--   Block unrolling of continuation values for finite-state routing of noiseless Gaussian observations
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $D=\dim_{\mathbb R}E$, and let $\gamma_E$ be the standard Gaussian measure on $E$ (centered, with identity covariance). Let $J$ be a finite set with a $\sigma$-algebra in which singletons are measurable, and let $\delta=(\delta_n)_{n\in\mathbb N}$ be transition maps $\delta_n:J\times(E\times\mathbb R)\to J$ such that $(x,y)\mapsto\delta_n(j,(x,y))$ is measurable for every $n$ and every $j$. Let $w=(w_n)_{n\in\mathbb N}$ be arbitrary functions $w_n:J\times E\to[0,\infty]$.
--
--   For $n,m\in\mathbb N$, $j\in J$ and an observation block $(A,b)\in E^m\times\mathbb R^m$, the *route* $R^{n,m}_\delta(j;A,b)\in J$ is the state reached from $j$ by feeding the observations $(A_1,b_1),\dots,(A_m,b_m)$ through the transitions $\delta_{n+1},\dots,\delta_{n+m}$: put $j_0=j$, $j_i=\delta_{n+i}\bigl(j_{i-1},(A_i,b_i)\bigr)$ for $1\le i\le m$, and $R^{n,m}_\delta(j;A,b)=j_m$. For $s\in E$ write $\langle s,A\rangle=(\langle s,A_1\rangle,\dots,\langle s,A_m\rangle)\in\mathbb R^m$ for the noiseless labels of the rows $A_i$.
--
--   The *continuation values* $V^{n,k}(j,s)\in[0,\infty]$ ($n,k\in\mathbb N$, $j\in J$, $s\in E$) are defined by recursion on $k$: $V^{n,0}(j,s)=w_n(j,s)$ and $V^{n,k+1}(j,s)=\int_E V^{n+1,k}\bigl(\delta_{n+1}(j,(x,\langle s,x\rangle)),s\bigr)\,d\gamma_E(x)$. Then for all $n,m,k\in\mathbb N$, $j\in J$ and $s\in E$,
--
--   $$
--   V^{n,m+k}(j,s)=\int_{E^m}V^{n+m,k}\Bigl(R^{n,m}_\delta\bigl(j;A,\langle s,A\rangle\bigr),\,s\Bigr)\,d\gamma_E^{\otimes m}(A).
--   $$
--
--   The identity integrates out the first $m$ steps of the recursion as one block of $m$ independent Gaussian rows, the remaining $k$ steps being summarized by $V^{n+m,k}$. For $k=0$ it gives the closed form $V^{n,m}(j,s)=\int_{E^m}w_{n+m}\bigl(R^{n,m}_\delta(j;A,\langle s,A\rangle),s\bigr)\,d\gamma_E^{\otimes m}(A)$: $V^{n,m}(j,s)$ is the expected weight $w_{n+m}(\cdot,s)$ at the state that a finite-state machine started in $j$ at time $n$ reaches after $m$ noiseless Gaussian observations of $s$. The block form is what allows a mass estimate for a single block of observations to be iterated along a long stream.
--
--   **Formalization Note** $V^{n,k}$ is `continuation δ w n k`, the route is `streamRoute δ n m j` (coordinates of $E^m$ are indexed by `Fin m`, starting at $0$), and the right-hand side is `blockValue (fun a => continuation δ w (n+m) k a) (streamRoute δ n m j) s`. All integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions, so no measurability of $w$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Stream.lean#L95-L119

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

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

theorem OAI.NoiselessRegression.continuation_unroll {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j))
    (n m k : ℕ) (j : J) (s : E) :
    continuation δ w n (m+k) j s =
      blockValue (fun a => continuation δ w (n+m) k a) (streamRoute δ n m j) s := by sorry
