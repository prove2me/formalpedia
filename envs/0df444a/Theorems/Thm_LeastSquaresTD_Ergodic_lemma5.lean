-- Prove2me | Theorems.Thm_LeastSquaresTD_Ergodic_lemma5
-- name    : LeastSquaresTD.Ergodic.lemma5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:18:17.615523+00:00
-- url     : https://prove2.me/theorems/9ce63eb2-4f09-40ca-8746-40e52e40d9d9
-- title:
--   Lemma 5 — LS TD converges w.p. 1 to [Φ'Π(I−γP)Φ]⁻¹[Φ'Πr̄] when states are visited i.o. in proportion π
-- statement:
--   Let $P$ be the transition matrix of any Markov chain on a finite nonempty state set $X$, with rewards $R$, expected rewards $\bar r$, features $\phi_x\in\mathbb R^m$ (rows of $\Phi$), discount factor $\gamma$ and weights $\pi$, $\Pi=\operatorname{diag}(\pi)$. Let $Z_0,Z_1,\dots$ be a Markov chain with transition matrix $P$ and some initial law, let $N_t(x)$ be the number of visits to $x$ among $Z_0,\dots,Z_{t-1}$, and let $\theta_t$ be the LS TD estimate (11) along $Z$. Suppose
--
--   1. with probability $1$, every state $x\in X$ is visited infinitely often ($N_t(x)\to\infty$);
--   2. with probability $1$, every state $x$ is visited in the long run in proportion $\pi_x$ ($N_t(x)/t\to\pi_x$);
--   3. $\Phi'\Pi(I-\gamma P)\Phi$ is invertible.
--
--   Then, with probability $1$,
--   $$\theta_{\rm LSTD}=\lim_{t\to\infty}\theta_t=\big[\Phi'\Pi(I-\gamma P)\Phi\big]^{-1}\big[\Phi'\Pi\bar r\big].$$
--
--   Lemma 5 reduces the convergence of LS TD to conditions on visit frequencies; Theorems 1 and 2 of the paper verify these conditions for absorbing and ergodic chains.
--
--   **Formalization Note** The paper's condition (1), "$\theta_t$ is found using algorithm LS TD", is the definition of $\theta_t$. The conclusion "$\theta_{\rm LSTD}=\ldots$" with $\theta_{\rm LSTD}\overset{\rm def}{=}\lim_t\theta_t$ (p. 42) is formalized as convergence to the right-hand side, which asserts that the limit exists.
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), p. 43, Lemma 5 (proved pp. 54–55, Appendix A)

import Mathlib
import Definitions.Def_LeastSquaresTD_Ergodic_Chain
import Definitions.Def_LeastSquaresTD_Ergodic_LSTD
open MeasureTheory Matrix Filter Topology

namespace LeastSquaresTD.Ergodic

/-- Lemma 5, p. 43: for any finite Markov chain, any initial law and any weights `π`, if with
probability 1 every state is visited infinitely often (condition (2)), with probability 1 every
state `x` is visited in the long run in proportion `πₓ` (condition (3)), and `Φ'Π(I − γP)Φ` is
invertible (condition (4)), then with probability 1 the LS TD estimates (11) converge to
`[Φ'Π(I − γP)Φ]⁻¹[Φ'Π r̄]`. -/
theorem lemma5 {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (R : X → X → ℝ) {m : ℕ} (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : X → ℝ) (hν : IsProbVec ν) (Z : ℕ → Ω → X) (hZ : IsMarkovLaw μ C ν Z)
    (h2 : ∀ᵐ ω ∂μ, ∀ x : X,
      Tendsto (fun t : ℕ => visitCount (fun k => Z k ω) x t) atTop atTop)
    (h3 : ∀ᵐ ω ∂μ, ∀ x : X,
      Tendsto (fun t : ℕ => (visitCount (fun k => Z k ω) x t : ℝ) / t) atTop (𝓝 (π x)))
    (h4 : IsUnit (lemma5Matrix C φ π γ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun t : ℕ => lstdTheta φ R γ t (fun k => Z k ω)) atTop
      (𝓝 ((lemma5Matrix C φ π γ)⁻¹ *ᵥ lemma5Vector C R φ π)) := by sorry

end LeastSquaresTD.Ergodic
