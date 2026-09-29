-- Prove2me | Theorems.Thm_MarkovMixing_countable_convergence
-- name    : MarkovMixing.countable_convergence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:40:59.665206+00:00
-- url     : https://prove2.me/theorems/704bcaaf-6d25-455f-969e-63a73756169b
-- title:
--   Convergence theorem on countable state spaces
-- statement:
--   Let $P$ be an irreducible and **aperiodic** Markov chain on a countable state space $V$ (nonnegative entries, rows summing to one as convergent series; every state reaches every other; the possible return times to each state have greatest common divisor one), and suppose some state is **positive recurrent**: its expected return time $\mathbb E_x(\tau^+_x)=\sum_{t\ge0}\mathbb P_x\{\tau^+_x>t\}$ is finite. Distances are measured in total variation via the $\ell^1$ formula $\|\mu-\nu\|_{TV}=\tfrac12\sum_y|\mu(y)-\nu(y)|$.
--
--   The theorem (Theorem 21.14 of Levin–Peres–Wilmer) asserts the existence of a distribution $\pi$ on $V$ such that:
--
--   1. $\pi$ is **stationary**: nonnegative, summing to one, with $\sum_x\pi(x)P(x,y)=\pi(y)$ for all $y$;
--   2. $\pi$ is the **unique** stationary distribution of the chain;
--   3. from **every** starting state $x$, $\;\bigl\|P^t(x,\cdot)-\pi\bigr\|_{TV}\to0$ as $t\to\infty$.
--
--   This is the Convergence Theorem of Mission II transplanted to countable state spaces, with positive recurrence supplying what finiteness gave for free. It is the fundamental theorem of applied Markov chain theory — queues, birth-and-death chains, random walks with drift — and the proof couples two copies of the chain on the product space, using aperiodicity and positive recurrence to force the copies to meet.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 21.3, Theorem 21.14, Eq. (21.9), p. 281

import Definitions.Def_mm_countable

namespace MarkovMixing

/-- **Theorem 21.14** (LPW): an irreducible, aperiodic, positive recurrent
chain on a countable state space has a unique stationary distribution `π`,
and `‖P^t(x,·) − π‖_TV → 0` for every starting state `x`. -/
theorem countable_convergence {V : Type*} [Countable V] [DecidableEq V]
    (P : V → V → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (hap : AperiodicC P) (x₀ : V) (hpos : PositiveRecurrent P x₀) :
    ∃ π : V → ℝ, IsStationaryC P π ∧
      (∀ π' : V → ℝ, IsStationaryC P π' → π' = π) ∧
      ∀ x : V, Filter.Tendsto
        (fun t => tvDistC (fun y => stepPow P t x y) π)
        Filter.atTop (nhds 0) := by
  sorry

end MarkovMixing
