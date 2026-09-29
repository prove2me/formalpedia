-- Prove2me | Theorems.Thm_MarkovMixing_distPairs_submultiplicative
-- name    : MarkovMixing.distPairs_submultiplicative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T15:16:20.345643+00:00
-- url     : https://prove2.me/theorems/09651dab-e035-4653-a90e-858c01ca0b0e
-- title:
--   Lemma 4.12 -- submultiplicativity of $\bar d$
-- statement:
--   Let $P$ be any stochastic matrix on a finite state space $V$ (nonnegative entries, rows summing to one), write $P^t(x,\cdot)$ for the row of the $t$-th matrix power — the distribution at time $t$ of the chain started at $x$ — and let
--   $$\bar d(t)=\max_{x,y\in V}\bigl\|P^t(x,\cdot)-P^t(y,\cdot)\bigr\|_{TV},\qquad \|\mu-\nu\|_{TV}=\max_{A\subseteq V}|\mu(A)-\nu(A)|,$$
--   be the **worst pairwise total variation distance** between two copies of the chain at time $t$.
--
--   The theorem (Lemma 4.12 of Levin–Peres–Wilmer) asserts that $\bar d$ is **submultiplicative**:
--   $$\bar d(s+t)\;\le\;\bar d(s)\cdot\bar d(t)\qquad\text{for all }s,t\in\mathbb N.$$
--   No irreducibility or aperiodicity is needed. Combined with the comparison $d\le\bar d\le 2d$ to the distance to stationarity, submultiplicativity is what makes distances decay geometrically past the mixing time, and hence what makes the mixing time a meaningful single parameter of a chain.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 4.4, Lemma 4.12, p. 54

import Definitions.Def_mm_mixing

namespace MarkovMixing

/-- **Lemma 4.12** (LPW): `d̄` is submultiplicative:
`d̄(s + t) ≤ d̄(s) · d̄(t)`. -/
theorem distPairs_submultiplicative {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (P : Matrix V V ℝ) (hP : IsStochastic P) (s t : ℕ) :
    distPairs P (s + t) ≤ distPairs P s * distPairs P t := by
  sorry

end MarkovMixing
