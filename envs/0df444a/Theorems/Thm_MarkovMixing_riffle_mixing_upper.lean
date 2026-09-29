-- Prove2me | Theorems.Thm_MarkovMixing_riffle_mixing_upper
-- name    : MarkovMixing.riffle_mixing_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:44:27.82395+00:00
-- url     : https://prove2.me/theorems/a11243a1-0fc5-4a49-9166-d36cec9de9af
-- title:
--   Proposition 8.13 -- the riffle shuffle mixes in $2\log_2 n+O(1)$
-- statement:
--   The **riffle shuffle** (Gilbert–Shannon–Reeds) of a deck of $n$ cards cuts the deck into two packets and interleaves them; it is formalized as the time reversal of the **inverse riffle**, in which every card independently receives a uniform bit and the cards labeled $0$ are pulled to the top, both packets keeping their relative order. (The reversal is legitimate because the stationary distribution — uniform over the $n!$ orderings — is preserved, and a walk and its reversal mix at the same speed.) The **mixing time** $t_{\mathrm{mix}}$ is the first time $t$ at which $\max_x\|P^t(x,\cdot)-\mathrm{unif}\|_{TV}\le\tfrac14$, with $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ the total variation distance.
--
--   The theorem (Proposition 8.13 of Levin–Peres–Wilmer) asserts: for every deck size $n\ge2$,
--   $$t_{\mathrm{mix}}\;\le\;2\log_2\!\Bigl(\frac{4n}{3}\Bigr)+1.$$
--   Order $\log_2 n$ riffle shuffles suffice — for a standard $52$-card deck this bound is in the famous "about seven shuffles" range. The proof tracks the bits accumulated by the inverse shuffles: once all $n$ bit-strings are distinct, the deck is exactly uniform.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 8.3.2, Proposition 8.13, p. 107

import Definitions.Def_mm_shuffle
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace MarkovMixing

/-- **Proposition 8.13** (LPW): for the riffle shuffle on an `n`-card deck,
`t_mix ≤ 2 log₂(4n/3) + 1`. -/
theorem riffle_mixing_upper (n : ℕ) (hn : 2 ≤ n) :
    (tMix (riffleShuffle n) (uniformDist (Equiv.Perm (Fin n))) : ℝ) ≤
      2 * Real.logb 2 (4 * n / 3) + 1 := by
  sorry

end MarkovMixing
