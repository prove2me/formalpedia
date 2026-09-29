-- Prove2me | Theorems.Thm_MarkovMixing_top_to_random_strong_stationary
-- name    : MarkovMixing.top_to_random_strong_stationary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:10:18.071038+00:00
-- url     : https://prove2.me/theorems/d7b80471-1c7c-4e36-92ad-55cb2e4d2ef9
-- title:
--   Proposition 6.1 -- $\tau_{top}$ is a strong stationary time
-- statement:
--   Consider the **top-to-random shuffle** of a deck of $n\ge2$ cards: at each step the top card is removed and reinserted at a position chosen uniformly at random among the $n$ possibilities. A **randomized stopping time** for a chain is a rule that, after observing the trajectory up to the present, decides (possibly with randomness) whether to stop now; such a rule is a **strong stationary time** if it is almost surely finite and the state at the moment of stopping is exactly stationary — here, a uniformly random deck — and independent of the stopping time itself.
--
--   The theorem (Proposition 6.1 together with Example 6.7 of Levin–Peres–Wilmer) asserts: for any starting deck, the following rule is a strong stationary time for the top-to-random shuffle — stop one shuffle after the card that was originally at the bottom of the deck first reaches the top. Intuition: each time a card is inserted below the original bottom card, it lands in a uniformly random relative position; by the time the original bottom card surfaces, the cards beneath it form a uniformly random arrangement, and one more insertion randomizes the whole deck.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 6.1, Proposition 6.1 and Example 6.7, pp. 75-78

import Definitions.Def_mm_stopping

namespace MarkovMixing

/-- **Proposition 6.1 and Example 6.7** (LPW): for the top-to-random shuffle,
the time `τ_top` — one shuffle after the original bottom card first reaches
the top of the deck — is a strong stationary time: the deck at time `τ_top`
is uniformly distributed and independent of `τ_top`. -/
theorem top_to_random_strong_stationary (n : ℕ) (hn : 2 ≤ n)
    (x : Equiv.Perm (Fin n)) :
    IsStrongStationaryTime (topToRandom n) (uniformDist (Equiv.Perm (Fin n))) x
      (topToRandomRule n) := by
  sorry

end MarkovMixing
