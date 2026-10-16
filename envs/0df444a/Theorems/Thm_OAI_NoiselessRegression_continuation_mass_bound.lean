-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_continuation_mass_bound
-- name    : OAI.NoiselessRegression.continuation_mass_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:41:18.217581+00:00
-- url     : https://prove2.me/theorems/7528c18e-5727-4e29-b991-c60579ab6ec3
-- title:
--   Polynomial ball-mass bounds propagate through finite-state routing of noiseless Gaussian observations
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $D=\dim_{\mathbb R}E$, and let $\gamma_E$ be the standard Gaussian measure on $E$ (centered, with identity covariance). Let $J$ be a nonempty finite set with a $\sigma$-algebra in which singletons are measurable, let $\mu$ be a finite measure on $E$, and let $\delta_n:J\times(E\times\mathbb R)\to J$ ($n\in\mathbb N$) be transition maps such that $(x,y)\mapsto\delta_n(j,(x,y))$ is measurable for all $n,j$. Let $w_n:J\times E\to[0,1]$ ($n\in\mathbb N$) be weights such that $w_n(j,\cdot)$ is measurable for all $n,j$.
--
--   Define the *continuation values* $V^{n,k}(j,s)\in[0,\infty]$ by $V^{n,0}(j,s)=w_n(j,s)$ and $V^{n,k+1}(j,s)=\int_E V^{n+1,k}\bigl(\delta_{n+1}(j,(x,\langle s,x\rangle)),s\bigr)\,d\gamma_E(x)$; thus $V^{n,k}(j,s)$ is the expected weight $w_{n+k}(\cdot,s)$ of the state reached from $j$ at time $n$ after $k$ transitions, each driven by a fresh Gaussian row $x$ together with its noiseless label $\langle s,x\rangle$. For a measurable $f:E\to[0,\infty]$ write $f\mu$ for the measure with density $f$ with respect to $\mu$. For a measure $\nu$ on $E$, $a\in\mathbb N$ and $C\in[0,\infty]$, say that $\nu$ has *polynomial ball mass* $(a,C)$ if $\nu(\bar B(z,r))\le C\,r^{a}$ for every $z\in E$ and every $r>0$, where $\bar B(z,r)$ is the closed ball of radius $r$ about $z$. For an integer $q\ge1$ put $K_q=32768^{D}\,|J|^{1/q}$.
--
--   Let $a,q\in\mathbb N$ and $C\in(0,\infty)$. Assume that $w_n(j,\cdot)\,\mu$ has polynomial ball mass $(a,C)$ for all $n\in\mathbb N$ and $j\in J$, and that $1\le D$, $a\le D$, $q\ge2$ and $2q\le a$. Then for all $n,k\in\mathbb N$ and $j\in J$ the measure $V^{n,k}(j,\cdot)\,\mu$ has polynomial ball mass $\bigl(a,\,C\,K_q^{\lfloor k/q\rfloor+1}\bigr)$, that is,
--
--   $$
--   \int_{\bar B(z,r)}V^{n,k}(j,s)\,d\mu(s)\le C\,\bigl(32768^{D}\,|J|^{1/q}\bigr)^{\lfloor k/q\rfloor+1}\,r^{a}\qquad\text{for all }z\in E\text{ and }r>0.
--   $$
--
--   Each block of $q$ observations costs at most one factor $K_q$, and the number of states enters only through $|J|^{1/q}$. Taking $\mu$ to be the uniform distribution on the unit sphere and $w$ the indicators of small balls around the points output in the various states, the theorem bounds the probability that a finite-state machine fed with noiseless Gaussian observations of a random unit vector ends in a state whose output is close to that vector.
--
--   **Formalization Note** The conclusion is `PolynomialMass (μ.withDensity (continuation δ w n k j)) a (C * streamFactor q ^ (k/q+1))`, where `PolynomialMass ν a C` means `ν (closedBall z r) ≤ C * ENNReal.ofReal (r^a)` for all `z` and all `r > 0`, `streamFactor q = 32768^(finrank ℝ E) * (card J)^(1/(q:ℝ))` uses a real exponent, and `k/q` is natural-number (floor) division. The constant $C$ is an extended nonnegative real assumed to be different from $0$ and $\infty$; $D$ is `Module.finrank ℝ E`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Stream.lean#L139-L192

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

theorem OAI.NoiselessRegression.continuation_mass_bound [Nonempty J] (μ : Measure E) [IsFiniteMeasure μ]
    {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (μ.withDensity (w n j)) a C)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    PolynomialMass (μ.withDensity (continuation δ w n k j)) a
      (C * streamFactor (E := E) (J := J) q ^ (k/q+1)) := by sorry
