-- Prove2me | Theorems.Thm_MarkovMixing_convergence_theorem
-- name    : MarkovMixing.convergence_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T15:17:00.673388+00:00
-- url     : https://prove2.me/theorems/e6e4a6fc-8c88-412d-ab44-e7690f865158
-- title:
--   Theorem 4.9 -- the Convergence Theorem
-- statement:
--   Let $P$ be the transition matrix of an **irreducible** and **aperiodic** Markov chain on a finite state space $V$ — irreducible meaning every state can reach every other in some number of steps, aperiodic meaning the return times to a state have greatest common divisor one — and let $\pi$ be a stationary distribution for $P$, i.e. $\sum_x\pi(x)P(x,y)=\pi(y)$ for all $y$. Write $P^t(x,\cdot)$ for the distribution of the chain at time $t$ started at $x$, and $\|\mu-\nu\|_{TV}=\max_{A\subseteq V}|\mu(A)-\nu(A)|$ for the total variation distance.
--
--   The theorem — the **Convergence Theorem** (Theorem 4.9 of Levin–Peres–Wilmer), the capstone of Chapter 4 — asserts that the chain converges to $\pi$ geometrically fast, uniformly in the starting state: there exist a rate $\alpha\in(0,1)$ and a constant $C>0$ such that
--   $$\max_{x\in V}\,\bigl\|P^t(x,\cdot)-\pi\bigr\|_{TV}\;\le\;C\,\alpha^{t}\qquad\text{for every }t\in\mathbb N.$$
--   In particular the stationary distribution of an irreducible aperiodic chain is unique and is reached from every starting point, with an error decaying exponentially in time — the statement that gives the mixing time its meaning, and the result all later chapters quantify.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 4.3, Theorem 4.9, p. 52

import Definitions.Def_mm_mixing

namespace MarkovMixing

/-- **Theorem 4.9, the Convergence Theorem** (LPW), the capstone of
Chapter 4: an irreducible, aperiodic finite chain converges to its stationary
distribution geometrically fast in total variation:
`max_x ‖P^t(x,·) − π‖_TV ≤ C αᵗ` for some `α ∈ (0,1)` and `C > 0`. -/
theorem convergence_theorem {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (hap : Aperiodic P) (π : V → ℝ) (hπ : IsStationary P π) :
    ∃ α : ℝ, α ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ t : ℕ, distStationary P π t ≤ C * α ^ t := by
  sorry

end MarkovMixing
