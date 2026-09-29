-- Prove2me | Theorems.Thm_MarkovMixing_random_transpositions_mixing
-- name    : MarkovMixing.random_transpositions_mixing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:44:01.851038+00:00
-- url     : https://prove2.me/theorems/de49e0a3-27db-47bb-b297-c697423d22fb
-- title:
--   Corollary 8.10 -- random transpositions mix in $(2+o(1))\,n\log n$
-- statement:
--   The **random transpositions shuffle** of a deck of $n$ cards picks two cards independently and uniformly at random and swaps them (doing nothing when the same card is picked twice): the identity is applied with probability $1/n$ and each transposition with probability $2/n^2$. Its stationary distribution is uniform over all $n!$ orderings. The **mixing time** $t_{\mathrm{mix}}$ is the first time $t$ at which $\max_x\|P^t(x,\cdot)-\mathrm{unif}\|_{TV}\le\tfrac14$, where $P^t(x,\cdot)$ is the law of the deck after $t$ shuffles from ordering $x$ and $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ is the total variation distance.
--
--   The theorem (Corollary 8.10 of Levin–Peres–Wilmer, the capstone of Chapter 8) asserts: for every $\delta>0$ there is an $N$ such that for all $n\ge N$,
--   $$t_{\mathrm{mix}}\;\le\;(2+\delta)\,n\log n.$$
--   Random transpositions mix in at most $(2+o(1))\,n\log n$ steps. The book's proof constructs a strong stationary time by the marking scheme of Broder; the matching lower bound of order $\tfrac12 n\log n$ is the companion theorem of this mission.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 8.2.2, Corollary 8.10, p. 104

import Definitions.Def_mm_shuffle
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Corollary 8.10** (LPW), the capstone of Chapter 8: the random
transpositions shuffle on `n` cards mixes in at most `(2 + o(1)) n log n`
steps. -/
theorem random_transpositions_mixing (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (tMix (randomTranspositions n) (uniformDist (Equiv.Perm (Fin n))) : ℝ) ≤
        (2 + δ) * n * Real.log n := by
  sorry

end MarkovMixing
