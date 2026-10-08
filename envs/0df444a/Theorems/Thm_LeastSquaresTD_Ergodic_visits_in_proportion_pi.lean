-- Prove2me | Theorems.Thm_LeastSquaresTD_Ergodic_visits_in_proportion_pi
-- name    : LeastSquaresTD.Ergodic.visits_in_proportion_pi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:17:55.259196+00:00
-- url     : https://prove2.me/theorems/c1ddba70-04e1-4d9f-8f7b-f7b6eff6b2d8
-- title:
--   Proof of Theorem 2, p. 45 — an ergodic chain visits every state infinitely often, in proportion π, with probability 1
-- statement:
--   Let $P$ be the transition matrix of an ergodic (irreducible) Markov chain on a finite nonempty state set $X$, and let $\pi$ be an invariant distribution of $P$. Let $Z_0,Z_1,\dots$ be a Markov chain with transition matrix $P$ and an arbitrary initial law $\nu$, and let $N_t(x)=\#\{k<t: Z_k=x\}$ be the number of visits to $x$ among the first $t$ states. Then:
--
--   1. with probability $1$, $N_t(x)\to\infty$ as $t\to\infty$ for every $x\in X$;
--   2. with probability $1$, for every $x\in X$,
--   $$\lim_{t\to\infty}\frac{N_t(x)}{t}=\pi_x .$$
--
--   This is the strong law of large numbers for the occupation times of a finite irreducible chain. In the proof of Theorem 2 it supplies conditions (2) and (3) of Lemma 5.
--
--   **Formalization Note** "Ergodic" is read as irreducible (periodic chains allowed). The statement is quantified over every initial law $\nu$, which contains Figure 3's arbitrary initial state $x_0$ (a point mass). Uniqueness of $\pi$ is not assumed; it follows from the conclusion.
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), p. 45, Proof of Theorem 2, first two sentences; p. 43 (π is the invariant distribution of P)

import Mathlib
import Definitions.Def_LeastSquaresTD_Ergodic_Chain
import Definitions.Def_LeastSquaresTD_Ergodic_LSTD
open MeasureTheory Matrix Filter Topology

namespace LeastSquaresTD.Ergodic

/-- Proof of Theorem 2, p. 45, first two sentences: on an ergodic (irreducible) finite chain,
started from any initial law, with probability 1 every state is visited infinitely often, and
with probability 1 the long-run fraction of time spent in each state `x` is `π x`, where `π` is
an invariant distribution of `P`. -/
theorem visits_in_proportion_pi {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (hC : C.IsErgodic) (π : X → ℝ) (hπ : C.IsStationary π)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : X → ℝ) (hν : IsProbVec ν) (Z : ℕ → Ω → X) (hZ : IsMarkovLaw μ C ν Z) :
    (∀ᵐ ω ∂μ, ∀ x : X,
      Tendsto (fun t : ℕ => visitCount (fun k => Z k ω) x t) atTop atTop) ∧
    (∀ᵐ ω ∂μ, ∀ x : X,
      Tendsto (fun t : ℕ => (visitCount (fun k => Z k ω) x t : ℝ) / t) atTop (𝓝 (π x))) := by sorry

end LeastSquaresTD.Ergodic
