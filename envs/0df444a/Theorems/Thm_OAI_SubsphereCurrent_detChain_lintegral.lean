-- Prove2me | Theorems.Thm_OAI_SubsphereCurrent_detChain_lintegral
-- name    : OAI.SubsphereCurrent.detChain_lintegral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:44:02.344041+00:00
-- url     : https://prove2.me/theorems/6d5f4947-5110-4ef7-86c3-31af56926ba5
-- title:
--   A coin-driven deterministic recursion realizes the law of a Markov chain
-- statement:
--   Let $A$ be a countable set with a $\sigma$-algebra in which all singletons are measurable (so every subset of $A$ is measurable), and let $\lambda_{[0,1)}$ be the uniform distribution on $[0,1)$. Suppose that for every step $m\in\mathbb{N}$ and every state $a\in A$ we are given a measurable map $F_m(a,\cdot):\mathbb{R}\to A$ and a probability mass function $K_m(a)$ on $A$ such that $F_m(a,U)$ has law $K_m(a)$ when $U$ is uniform on $[0,1)$, i.e. $(F_m(a,\cdot))_{\#}\lambda_{[0,1)}=K_m(a)$ for all $m$ and $a$.
--
--   For a starting state $a$ and coins $r=(r_0,\dots,r_{n-1})\in\mathbb{R}^n$, define the deterministic chain $a_0=a$, $a_{m+1}=F_m(a_m,r_m)$, and put $D_n(a,r)=a_n$. Let $P^a_n$ be the law at time $n$ of the time-inhomogeneous Markov chain with kernels $K_0,K_1,\dots$ started at $a$: $P^a_0=\delta_a$ and $P^a_{m+1}(c)=\sum_{b\in A}P^a_m(b)\,K_m(b)(c)$.
--
--   **Theorem.** For every $a\in A$, every $n\in\mathbb{N}$ and every function $f:A\to[0,\infty]$,
--   $$
--   \int_{\mathbb{R}^n}f\bigl(D_n(a,r)\bigr)\,d\lambda_{[0,1)}^{\otimes n}(r)=\int_A f\,dP^a_n\ \Bigl(=\sum_{b\in A}P^a_n(b)\,f(b)\Bigr).
--   $$
--
--   In words: when the coins are independent and uniform on $[0,1)$, the deterministic recursion $D_n(a,\cdot)$ has exactly the law $P^a_n$ of the Markov chain. This is the general bookkeeping step that converts a randomized finite-state run into a deterministic run on a random coin tape.
--
--   **Formalization Note** The chain is `detChain F a n r`, which applies `F n` to the value for the first $n$ coins and to the last coin; the law is `lawChain K a n`, built with `PMF.bind`, and the hypothesis is the equality of measures `coinLaw.map (F n a) = (K n a).toMeasure`. No measurability assumption on $f$ is needed because every function on a countable space with measurable singletons is measurable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Kernels/Precision.lean#L374-L395

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

open OAI OAI.SubsphereCurrent
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
variable {A : Type*} [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A]

theorem OAI.SubsphereCurrent.detChain_lintegral {F : ℕ → A → ℝ → A} {K : ℕ → A → PMF A}
    (hF : ∀ n a, Measurable (F n a))
    (hFK : ∀ n a, coinLaw.map (F n a) = (K n a).toMeasure)
    (a : A) (n : ℕ) (f : A → ℝ≥0∞) :
    (∫⁻ r : Fin n → ℝ, f (detChain F a n r) ∂Measure.pi (fun _ => coinLaw)) =
      ∫⁻ b, f b ∂(lawChain K a n).toMeasure := by sorry
