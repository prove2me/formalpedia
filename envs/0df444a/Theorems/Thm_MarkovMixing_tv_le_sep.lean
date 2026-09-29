-- Prove2me | Theorems.Thm_MarkovMixing_tv_le_sep
-- name    : MarkovMixing.tv_le_sep
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:10:47.089521+00:00
-- url     : https://prove2.me/theorems/ad131be4-b254-4418-ba81-65c9ec699085
-- title:
--   Lemma 6.13 -- total variation is bounded by separation
-- statement:
--   Let $P$ be a Markov chain on a finite state space $V$ with strictly positive stationary distribution $\pi$. Write $P^t(x,\cdot)$ for the distribution at time $t$ started at $x$, $\|\mu-\nu\|_{TV}=\max_{A\subseteq V}|\mu(A)-\nu(A)|$ for the total variation distance, and
--   $$s_x(t)=\max_{y\in V}\Bigl(1-\frac{P^t(x,y)}{\pi(y)}\Bigr)$$
--   for the **separation distance** at time $t$ from the starting state $x$.
--
--   The theorem (Lemma 6.13 of Levin–Peres–Wilmer) asserts that separation dominates total variation: for every starting state $x$ and every time $t$,
--   $$\bigl\|P^t(x,\cdot)-\pi\bigr\|_{TV}\;\le\;s_x(t).$$
--   Consequently any bound on the separation distance — for instance one obtained from a strong stationary time — is automatically a bound on the total variation distance to stationarity.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 6.4, Lemma 6.13, p. 80

import Definitions.Def_mm_stopping

namespace MarkovMixing

/-- **Lemma 6.13** (LPW): total variation distance to stationarity is bounded
by the separation distance: `‖P^t(x,·) − π‖_TV ≤ s_x(t)`. -/
theorem tv_le_sep {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π) (hpos : ∀ y : V, 0 < π y)
    (x : V) (t : ℕ) :
    tvDist (rowDist P t x) π ≤ sepDist P π x t := by
  sorry

end MarkovMixing
