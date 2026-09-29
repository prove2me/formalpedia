-- Prove2me | Theorems.Thm_MarkovMixing_riffle_mixing_lower
-- name    : MarkovMixing.riffle_mixing_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:44:38.925837+00:00
-- url     : https://prove2.me/theorems/ea70b377-f5b6-4ba9-93fd-e4886d85282a
-- title:
--   Proposition 8.14 -- the riffle shuffle needs $\log_2 n$ shuffles
-- statement:
--   The **riffle shuffle** (Gilbert–Shannon–Reeds) of a deck of $n$ cards cuts the deck into two packets and interleaves them; formally it is the time reversal of the inverse riffle, in which each card independently receives a uniform bit and the cards labeled $0$ move to the top preserving relative order. Its stationary distribution is uniform. For a tolerance $\varepsilon$, the **mixing time** $t_{\mathrm{mix}}(\varepsilon)$ is the first $t$ with $\max_x\|P^t(x,\cdot)-\mathrm{unif}\|_{TV}\le\varepsilon$, where $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$.
--
--   The theorem (Proposition 8.14 of Levin–Peres–Wilmer) asserts: for any fixed tolerances $0<\varepsilon<1$ and margin $0<\delta<1$ there is an $N$ such that for all $n\ge N$,
--   $$t_{\mathrm{mix}}(\varepsilon)\;\ge\;(1-\delta)\,\log_2 n.$$
--   So the upper bound $2\log_2(4n/3)+1$ of the companion theorem is sharp up to the constant factor $2$: no fixed number of riffle shuffles suffices for all deck sizes, and $\log_2 n$ is the true order. The obstruction is counting: $t$ shuffles produce at most $2^{nt}$ equally likely bit-histories, too few to spread mass over $n!$ orderings until $t\gtrsim\log_2 n$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 8.3.3, Proposition 8.14, p. 110

import Definitions.Def_mm_shuffle
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace MarkovMixing

/-- **Proposition 8.14** (LPW): for the riffle shuffle on an `n`-card deck
and fixed `0 < ε, δ < 1`, for sufficiently large `n`,
`t_mix(ε) ≥ (1 − δ) log₂ n`. -/
theorem riffle_mixing_lower (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 - δ) * Real.logb 2 n ≤
        (mixingTime (riffleShuffle n) (uniformDist (Equiv.Perm (Fin n))) ε : ℝ) := by
  sorry

end MarkovMixing
