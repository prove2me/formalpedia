-- Prove2me | Theorems.Thm_MarkovMixing_positive_recurrent_iff_stationary
-- name    : MarkovMixing.positive_recurrent_iff_stationary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:40:36.950899+00:00
-- url     : https://prove2.me/theorems/ef3abe04-7ca1-4df8-9c5f-dc9052d978fe
-- title:
--   Positive recurrence $\iff$ stationary distribution
-- statement:
--   Let $P$ be an irreducible Markov chain on a **countable** state space $V$ (nonnegative entries, rows summing to one as convergent series, every state reaching every other). A state $x$ is **positive recurrent** when its expected return time is finite: with $\tau^+_x=\min\{t\ge1:X_t=x\}$, the tail-sum formula $\mathbb E_x(\tau^+_x)=\sum_{t\ge0}\mathbb P_x\{\tau^+_x>t\}$ converges. A **stationary distribution** is a nonnegative $\pi$ summing to one with $\sum_x\pi(x)P(x,y)=\pi(y)$ for every $y$ (all as convergent series).
--
--   The theorem (Theorem 21.12 of Levin–Peres–Wilmer) asserts: a state is positive recurrent **if and only if** the chain admits a stationary distribution.
--
--   On infinite state spaces, existence of a stationary distribution — automatic in the finite theory of Mission I — becomes a genuine dichotomy: simple random walk on $\mathbb Z$ is recurrent but has infinite expected return times and no stationary distribution, while a positively drifting queue may fail even to be recurrent. The proof constructs $\pi$ from expected visit counts during one excursion from $x$ (normalized by $\mathbb E_x(\tau^+_x)$, finite exactly under positive recurrence), and conversely reads finiteness of $\mathbb E_x(\tau^+_x)=1/\pi(x)$ off Kac's lemma. Since positive recurrence of one state is thereby equivalent to a state-free condition, it too is a class property.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 21.3, Theorem 21.12, p. 280

import Definitions.Def_mm_countable

namespace MarkovMixing

/-- **Theorem 21.12** (LPW): an irreducible chain on a countable state space
is positive recurrent if and only if it has a stationary (probability)
distribution. -/
theorem positive_recurrent_iff_stationary {V : Type*} [Countable V]
    [DecidableEq V] (P : V → V → ℝ) (hP : IsStochasticC P)
    (hirr : IrreducibleC P) (x : V) :
    PositiveRecurrent P x ↔ ∃ π : V → ℝ, IsStationaryC P π := by
  sorry

end MarkovMixing
