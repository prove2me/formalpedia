-- Prove2me | Theorems.Thm_MarkovMixing_top_to_random_mixing
-- name    : MarkovMixing.top_to_random_mixing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:11:14.619483+00:00
-- url     : https://prove2.me/theorems/f4f8a021-e574-4ce0-9b76-5c7490602c14
-- title:
--   Section 6.5.3 -- the top-to-random shuffle mixes in $n\log n+cn$ steps
-- statement:
--   Consider the **top-to-random shuffle** of a deck of $n\ge2$ cards: at each step the top card is removed and reinserted at a uniformly random position. Its stationary distribution is uniform over all $n!$ orderings. Write $P^t(x,\cdot)$ for the law of the deck after $t$ shuffles started from the ordering $x$, $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ for the total variation distance, and $d(t)=\max_x\|P^t(x,\cdot)-\mathrm{unif}\|_{TV}$ for the worst-case distance to uniformity.
--
--   The theorem (§6.5.3, display (6.16) of Levin–Peres–Wilmer, the capstone of Chapters 5–6) asserts: for every $\alpha>0$,
--   $$d\bigl(\lceil n\log n+\alpha n\rceil\bigr)\;\le\;e^{-\alpha}.$$
--   After $n\log n$ shuffles plus any linear-in-$n$ margin, the deck is exponentially close to uniform in the margin: $n\log n$ top-to-random shuffles suffice. The proof runs through the strong stationary time of this mission — one shuffle after the original bottom card surfaces — whose tail is controlled by the coupon-collector bounds of Mission I.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 6.5.3, Eq. (6.16), p. 81

import Definitions.Def_mm_stopping
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **§6.5.3, Eq. (6.16)** (LPW), the capstone of Chapters 5–6: for the
top-to-random shuffle on `n` cards,
`d(⌈n log n + α n⌉) ≤ e^{-α}` for every `α > 0`. -/
theorem top_to_random_mixing (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α) :
    distStationary (topToRandom n) (uniformDist (Equiv.Perm (Fin n)))
      ⌈(n : ℝ) * Real.log n + α * n⌉₊ ≤ Real.exp (-α) := by
  sorry

end MarkovMixing
