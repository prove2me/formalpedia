-- Prove2me | Theorems.Thm_MarkovMixing_recurrence_dichotomy
-- name    : MarkovMixing.recurrence_dichotomy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:40:26.506411+00:00
-- url     : https://prove2.me/theorems/a0e14d8a-0af3-4342-aa41-9415ee34abf7
-- title:
--   The recurrence dichotomy via Green's functions
-- statement:
--   Let $P$ be an irreducible Markov chain on a **countable** state space $V$: nonnegative entries with each row summing to one as a convergent series, and every state reaching every other at some time. For a state $x$, the **first return time** is $\tau^+_x=\min\{t\ge1:X_t=x\}$; the state is **recurrent** when return is certain, $\mathbb P_x\{\tau^+_x>t\}\to0$ as $t\to\infty$, and **transient** otherwise. The **Green's function** at $x$ is the expected number of visits to $x$,
--   $$G(x,x)=\sum_{t=0}^{\infty}P^t(x,x).$$
--
--   The theorem (Proposition 21.3 of Levin–Peres–Wilmer) asserts:
--
--   1. a state $x$ is recurrent **if and only if** its Green's series diverges — equivalently, transience is exactly summability of the return probabilities $P^t(x,x)$;
--   2. recurrence is a class property: if one state of the irreducible chain is recurrent, every state is.
--
--   The equivalence comes from the renewal structure: the number of returns to $x$ is geometric with success probability $\mathbb P_x\{\tau^+_x<\infty\}$, so its expectation $G(x,x)$ is finite exactly when return is uncertain. This dichotomy is the standard tool for deciding recurrence — Pólya's theorem, the goal of this mission, is proved by estimating the series $\sum_tP^t(0,0)\asymp\sum_tt^{-d/2}$ for the walk on $\mathbb Z^d$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 21.1, Proposition 21.3, p. 276

import Definitions.Def_mm_countable

namespace MarkovMixing

/-- **Proposition 21.3** (LPW): for an irreducible chain on a countable
state space, a state is recurrent if and only if its Green's function
`G(x,x) = ∑_t P^t(x,x)` diverges, and recurrence of one state implies
recurrence of all states. -/
theorem recurrence_dichotomy {V : Type*} [Countable V] [DecidableEq V]
    (P : V → V → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P) (x : V) :
    (Recurrent P x ↔ ¬Summable fun t => stepPow P t x x) ∧
    (Recurrent P x → ∀ y : V, Recurrent P y) := by
  sorry

end MarkovMixing
