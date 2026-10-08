-- Prove2me | Theorems.Thm_KendallQueues_GIMs_theorem1_ergodic_geometric
-- name    : KendallQueues.GIMs.theorem1_ergodic_geometric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:45:32.650991+00:00
-- url     : https://prove2.me/theorems/73decc65-afc5-4b72-8189-08e591e98ae5
-- title:
--   Theorem I, p. 349 — for ρ < 1 the GI/M/s chain is ergodic with a geometric limiting distribution
-- statement:
--   Consider GI/M/s with $s\ge1$ servers, inter-arrival law $A$ on $[0,\infty)$ with mean $a\in(0,\infty)$ and negative-exponential service of mean $b>0$, and let $P$ be the transition matrix (8)–(14) of the chain imbedded at arrival epochs. Suppose the relative traffic intensity is less than unity,
--   $$\rho=\frac{b}{sa}<1.$$
--   Then the chain is irreducible and ergodic (aperiodic and positive recurrent). There is a limiting distribution $\pi=(\pi_0,\pi_1,\dots)$, with $\pi_j>0$ and $\sum_j\pi_j=1$, such that $p^n_{ij}\to\pi_j$ as $n\to\infty$ for all $i,j$. Moreover the equation
--   $$F(\lambda)=\lambda,\qquad F(\lambda)=\int_0^\infty e^{-(1-\lambda)su/b}\,dA(u),$$
--   has a unique root $\lambda$ in $0<\lambda<1$, and $\pi$ is a geometric series with common ratio $\lambda$ save for modifications to its first $s-1$ terms: there is $C>0$ with
--   $$\pi_j=C\lambda^{\,j-(s-1)}\qquad(j\ge s-1).$$
--
--   This is the principal result about the imbedded chain; Theorems II–IV are read off from it.
--
--   **Formalization Note** "Ergodic" is Feller's: aperiodic and positive recurrent (the published predicates `Aperiodic` and `PositiveRecurrent`). The chain is any `TransitionMatrix` with `P.p = gimsMatrix s A b`. "The first $s-1$ terms" are the states $0,\dots,s-2$, as in the trial vector (15).
-- source:
--   Kendall (Ann. Math. Statist. 24, 1953), §7, p. 349, Theorem I

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime
import Definitions.Def_KendallQueues_GIMs_Model

open MeasureTheory Filter Topology
open QueueingFundamentals.Foundations QueueingFundamentals.GM1

namespace KendallQueues.GIMs

/-- Theorem I, p. 349: when `ρ < 1` the GI/M/s imbedded chain is irreducible and ergodic
(aperiodic and positive recurrent); its limiting distribution is positive, sums to one, and is
geometric from the state `s - 1` on, with common ratio the unique root of `F(λ) = λ` in `(0, 1)`. -/
theorem theorem1_ergodic_geometric (s : ℕ) (hs : 1 ≤ s) (A : Measure ℝ) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hA : IsInterarrivalLaw A a⁻¹) (hρ : rho s a b < 1)
    (P : TransitionMatrix) (hP : P.p = gimsMatrix s A b) :
    P.Irreducible ∧ P.Aperiodic ∧ P.PositiveRecurrent ∧
      ∃ π : ℕ → ℝ, (∀ j, 0 < π j) ∧ HasSum π 1 ∧
        (∀ i j, Tendsto (fun n => P.stepProb n i j) atTop (𝓝 (π j))) ∧
        ∃ lam : ℝ, lam ∈ Set.Ioo (0 : ℝ) 1 ∧ F s A b lam = lam ∧
          (∀ y : ℝ, y ∈ Set.Ioo (0 : ℝ) 1 → F s A b y = y → y = lam) ∧
          ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, s - 1 ≤ j → π j = C * lam ^ (j - (s - 1)) := by sorry

end KendallQueues.GIMs
