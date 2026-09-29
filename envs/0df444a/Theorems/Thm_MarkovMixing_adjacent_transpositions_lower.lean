-- Prove2me | Theorems.Thm_MarkovMixing_adjacent_transpositions_lower
-- name    : MarkovMixing.adjacent_transpositions_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:45:02.698577+00:00
-- url     : https://prove2.me/theorems/30e66799-0e40-45c9-a162-a2f92e2901d3
-- title:
--   Section 16.1.3 -- adjacent transpositions lower bound
-- statement:
--   The **lazy random adjacent transpositions shuffle** of a deck of $n$ cards does nothing with probability $\tfrac12$ and otherwise swaps the cards in a uniformly chosen pair of neighbouring positions $(i,i+1)$: the identity carries probability $\tfrac12$ and each of the $n-1$ adjacent transpositions probability $1/\bigl(2(n-1)\bigr)$. Its stationary distribution is uniform. The **mixing time** $t_{\mathrm{mix}}$ is the first time $t$ at which $\max_x\|P^t(x,\cdot)-\mathrm{unif}\|_{TV}\le\tfrac14$, with $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ the total variation distance.
--
--   The theorem (§16.1.3 of Levin–Peres–Wilmer) asserts: for every $n\ge2$,
--   $$t_{\mathrm{mix}}\;\ge\;\frac{n^2\,(n-1)}{16}.$$
--   Order $n^3$ steps are necessary, matching the $n^3\log n$ upper bound up to the logarithm. The obstruction is transport: a single card performs a random walk on the $n$ positions that advances only when its own position is selected, so moving it across the deck takes order $n\cdot n^2$ steps.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 16.1.3, pp. 219-220

import Definitions.Def_mm_shuffle

namespace MarkovMixing

/-- **§16.1.3** (LPW): for the lazy random adjacent transpositions shuffle
on `n` cards, `t_mix ≥ n²(n−1)/16`. -/
theorem adjacent_transpositions_lower (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 16 ≤
      (tMix (groupWalk (adjacentTranspositionDist n))
        (uniformDist (Equiv.Perm (Fin n))) : ℝ) := by
  sorry

end MarkovMixing
