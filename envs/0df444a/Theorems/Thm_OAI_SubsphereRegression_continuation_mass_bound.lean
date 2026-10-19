-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_continuation_mass_bound
-- name    : OAI.SubsphereRegression.continuation_mass_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:34:02.022933+00:00
-- url     : https://prove2.me/theorems/32f7d1fe-10e1-429f-8735-eb13c032550c
-- title:
--   Polynomial ball growth propagates along stream continuations, one factor per block
-- statement:
--   Let $E$ be a real inner product space of finite dimension $d$ with its Borel $\sigma$-algebra and standard Gaussian measure $\gamma_E$, and let $J$ be a nonempty finite set carrying a $\sigma$-algebra in which singletons are measurable. For a measure $\nu$ on $E$, $a\in\mathbb{N}$ and $C\in[0,\infty]$, say that $\nu$ has *polynomial ball growth* $(a,C)$ if $\nu(\bar B(z,r))\le C\,r^a$ for all $z\in E$ and $r>0$. For a measure $\mu$ and $f:E\to[0,\infty]$, write $f\mu$ for the measure with density $f$, $(f\mu)(S)=\int_S f\,d\mu$.
--
--   Let $\delta=(\delta_t)_{t\in\mathbb{N}}$, $\delta_t:J\times(E\times\mathbb{R})\to J$, be a transition rule and $w_t:J\times E\to[0,\infty]$ weights, and let $V_{n,k}(j,s)$ be the *continuation*: $V_{n,0}(j,s)=w_n(j,s)$ and $V_{n,k+1}(j,s)=\int_E V_{n+1,k}\bigl(\delta_{n+1}(j,(x,\langle s,x\rangle)),s\bigr)\,d\gamma_E(x)$. For $q\in\mathbb{N}$ put $K_q=32768^{d}\,|J|^{1/q}$.
--
--   Let $a,q\in\mathbb{N}$ and $C\in[0,\infty]$. Assume that $\mu$ is a finite Borel measure on $E$; every map $\delta_t(j,\cdot)$ and every $w_t(j,\cdot)$ is measurable; $w_t(j,s)\le1$ for all $t,j,s$; $0<C<\infty$; every measure $w_t(j,\cdot)\,\mu$ has polynomial ball growth $(a,C)$; and $d\ge1$, $a\le d$, $q\ge2$, $2q\le a$. Then for all $n,k\in\mathbb{N}$ and $j\in J$ the measure $V_{n,k}(j,\cdot)\,\mu$ has polynomial ball growth $\bigl(a,\,C\,K_q^{\lfloor k/q\rfloor+1}\bigr)$, that is,
--
--   $$
--   \int_{\bar B(z,r)}V_{n,k}(j,s)\,d\mu(s)\;\le\;C\,K_q^{\lfloor k/q\rfloor+1}\,r^{a}\qquad\text{for all }z\in E\text{ and }r>0.
--   $$
--
--   Each block of $q$ consecutive steps costs at most one factor $K_q$, so after $k$ steps the growth constant is controlled by the number $\lfloor k/q\rfloor+1$ of blocks. When $|J|=2^M$, $K_q=2^{15d+M/q}$, which is $2^{O(d)}$ when $q$ is proportional to $d$ and $M=O(d^2)$; this is how a memory budget of order $d^2$ bits enters the sample lower bound.
--
--   **Formalization Note** Polynomial ball growth is `PolynomialMass`, $f\mu$ is `μ.withDensity f`, $K_q$ is `streamFactor q`, and $\lfloor k/q\rfloor$ is natural-number division `k/q`. All quantities are extended nonnegative reals; $C\ne0$ and $C\ne\infty$ are separate hypotheses.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Streaming.lean#L130-L183

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

theorem OAI.SubsphereRegression.continuation_mass_bound [Nonempty J] (μ : Measure E) [IsFiniteMeasure μ]
    {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (μ.withDensity (w n j)) a C)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    PolynomialMass (μ.withDensity (continuation δ w n k j)) a
      (C * streamFactor (E := E) (J := J) q ^ (k/q+1)) := by sorry
