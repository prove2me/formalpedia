-- Prove2me | Theorems.Thm_LeastSquaresTD_Ergodic_lstd_limit_of_pair_frequencies
-- name    : LeastSquaresTD.Ergodic.lstd_limit_of_pair_frequencies
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:18:01.613777+00:00
-- url     : https://prove2.me/theorems/0cd3f36b-1f1f-4ab0-a5e6-0308210467d3
-- title:
--   Proof of Lemma 5, pp. 54–55 — LS TD converges to [Φ'Π(I−γP)Φ]⁻¹[Φ'Πr̄] along a path with transition frequencies πₓP(x,y)
-- statement:
--   Let $P$ be the transition matrix of a Markov chain on a finite state set $X$, with rewards $R(x,y)$, expected rewards $\bar r_x=\sum_yP(x,y)R(x,y)$, features $\phi_x\in\mathbb R^m$ (rows of $\Phi$), a discount factor $\gamma$ and weights $\pi$ on $X$, $\Pi=\operatorname{diag}(\pi)$. Let $z_0,z_1,\dots$ be a sequence of states such that, for all $x,y\in X$, the fraction of the first $t$ transitions that go from $x$ to $y$ satisfies
--   $$\lim_{t\to\infty}\frac{\#\{k<t: z_k=x,\ z_{k+1}=y\}}{t}=\pi_x\,P(x,y),$$
--   and suppose $\Phi'\Pi(I-\gamma P)\Phi$ is invertible. Then the LS TD estimates $\theta_t$ of (11) computed along $z$ satisfy
--   $$\lim_{t\to\infty}\theta_t=\big[\Phi'\Pi(I-\gamma P)\Phi\big]^{-1}\big[\Phi'\Pi\bar r\big].$$
--
--   This is the deterministic core of the proof of Lemma 5: the averages in (11) are sums over pairs of states weighted by the empirical transition frequencies, and matrix inversion is continuous at an invertible matrix.
--
--   **Formalization Note** The proof's two inputs, "the sampled transition probabilities between each pair of states approaches the true transition probabilities" and "each state is visited in the proportion $\pi_x$", are combined into the single hypothesis on transition frequencies. The paper's $\bar R$ (p. 55) is $\bar r$.
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), pp. 54–55, Appendix A, Proof of Lemma 5, displayed chain of equalities

import Mathlib
import Definitions.Def_LeastSquaresTD_Ergodic_Chain
import Definitions.Def_LeastSquaresTD_Ergodic_LSTD
open MeasureTheory Matrix Filter Topology

namespace LeastSquaresTD.Ergodic

/-- Proof of Lemma 5, pp. 54–55 (the displayed chain of equalities), pathwise: if along a path
`z` the frequency of each transition `x → y` among the first `t` transitions tends to
`πₓ P(x,y)`, and `Φ'Π(I − γP)Φ` is invertible, then the LS TD estimates (11) converge to
`[Φ'Π(I − γP)Φ]⁻¹[Φ'Π r̄]`. -/
theorem lstd_limit_of_pair_frequencies {X : Type*} [Fintype X] [DecidableEq X]
    (C : Chain X) (R : X → X → ℝ) {m : ℕ} (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ)
    (z : ℕ → X)
    (hfreq : ∀ x y : X,
      Tendsto (fun t : ℕ => (pairCount z x y t : ℝ) / t) atTop (𝓝 (π x * C.P x y)))
    (hM : IsUnit (lemma5Matrix C φ π γ)) :
    Tendsto (fun t : ℕ => lstdTheta φ R γ t z) atTop
      (𝓝 ((lemma5Matrix C φ π γ)⁻¹ *ᵥ lemma5Vector C R φ π)) := by sorry

end LeastSquaresTD.Ergodic
