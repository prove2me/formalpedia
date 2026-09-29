-- Prove2me | Theorems.Thm_MarkovMixing_kac_lemma
-- name    : MarkovMixing.kac_lemma
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:40:48.248305+00:00
-- url     : https://prove2.me/theorems/d08379a7-654c-48e4-99e5-8d21df55e49e
-- title:
--   Kac's lemma
-- statement:
--   Let $P$ be an irreducible Markov chain on a **countable** state space $V$ (nonnegative entries, rows summing to one as convergent series, every state reaching every other), and suppose $\pi$ is a stationary distribution for it: nonnegative, summing to one, with $\sum_x\pi(x)P(x,y)=\pi(y)$ for every $y$. For a nonempty set of states $S$ and $x\in S$, the **first return time to $S$** is $\tau^+_S=\min\{t\ge1:X_t\in S\}$, with expectation given by the tail-sum formula $\mathbb E_x(\tau^+_S)=\sum_{t\ge0}\mathbb P_x\{\tau^+_S>t\}$.
--
--   The theorem (**Kac's lemma**, Lemma 21.13 of Levin–Peres–Wilmer) asserts the exact identity
--   $$\sum_{x\in S}\pi(x)\,\mathbb E_x\bigl(\tau^+_S\bigr)\;=\;1,$$
--   the series over $S$ converging to exactly $1$.
--
--   Started from stationarity conditioned on being in $S$, the expected time to return to $S$ is exactly $1/\pi(S)$ — and for a singleton, $\mathbb E_x(\tau^+_x)=1/\pi(x)$: stationary mass is inverse return time. The identity is a mass-transport double count — every time-step of the stationary chain is the $k$-th step of exactly one excursion from $S$ — and it is the quantitative link between stationary distributions and return times that drives the positive-recurrence theory of this mission.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 21.3, Lemma 21.13, Eq. (21.5), p. 280

import Definitions.Def_mm_countable

namespace MarkovMixing

/-- **Lemma 21.13 (Kac)** (LPW): for an irreducible chain with stationary
distribution `π` and any nonempty set `S` of states,
`∑_{x ∈ S} π(x) E_x(τ⁺_S) = 1`. -/
theorem kac_lemma {V : Type*} [Countable V] [DecidableEq V]
    (P : V → V → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (π : V → ℝ) (hπ : IsStationaryC P π) (S : Set V) (hS : S.Nonempty) :
    HasSum (fun x : S => π x.1 * expSetReturnC P x.1 S) 1 := by
  sorry

end MarkovMixing
