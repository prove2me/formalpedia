-- Prove2me | Theorems.Thm_MarkovMixing_l_reversal_lower
-- name    : MarkovMixing.l_reversal_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:45:17.022976+00:00
-- url     : https://prove2.me/theorems/331a8b2f-0761-4eee-9f5b-66088b9e1f1f
-- title:
--   Proposition 16.2 -- the $L$-reversal chain is far from mixed at $(1-\varepsilon)\frac n2\log n$
-- statement:
--   The **$L$-reversal chain** shuffles a circular arrangement of $n$ cards (an arrangement indexed by $\mathbb Z_n$): at each step it picks a starting position $i\in\mathbb Z_n$ and a length $k\in\{0,\dots,L-1\}$ uniformly at random and reverses the circular arc of cards from position $i$ to position $i+k$, leaving the rest fixed. Its stationary distribution is uniform. Write $P^t(x,\cdot)$ for the law after $t$ moves from the arrangement $x$, $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ for the total variation distance, and $d_n(t)=\max_x\|P^t(x,\cdot)-\mathrm{unif}\|_{TV}$ for the chain on $n$ cards.
--
--   The theorem (Proposition 16.2 of Levin–Peres–Wilmer) asserts: for any family of maximal reversal lengths $L(n)$ with $1\le L(n)<n/2$ and any fixed $0<\varepsilon<1$, evaluating each chain at time $t_n=\bigl\lfloor(1-\varepsilon)\,\tfrac n2\log n\bigr\rfloor$ gives
--   $$d_n(t_n)\;\longrightarrow\;1\qquad(n\to\infty).$$
--   Before time $\tfrac n2\log n$ the chain is asymptotically as far from uniform as possible, whatever $L$ is. The witness is again coupon-collector-flavoured: cards whose neighbourhood no reversal has yet touched retain their original neighbours in the circular order. (In the formal statement the deck sizes are enumerated as $n=m+2$, $m\to\infty$, so that $n\ge2$ automatically.)
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 16.2.1, Proposition 16.2, p. 222

import Definitions.Def_mm_shuffle
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Proposition 16.2** (LPW): for the family of `L`-reversal chains with
`1 ≤ L(n) < n/2` and any fixed `0 < ε < 1`, at time
`t(n) = (1−ε)(n/2) log n` the distance to stationarity tends to `1`:
the chain is far from mixed.  (States are indexed by `m` with `n = m + 2`.) -/
theorem l_reversal_lower (L : ℕ → ℕ)
    (hL : ∀ n : ℕ, 3 ≤ n → 1 ≤ L n ∧ 2 * L n < n)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    Filter.Tendsto
      (fun m : ℕ =>
        distStationary (groupWalk (lReversalDist (m + 2) (L (m + 2))))
          (uniformDist (Equiv.Perm (ZMod (m + 2))))
          ⌊(1 - ε) * ((m : ℝ) + 2) / 2 * Real.log ((m : ℝ) + 2)⌋₊)
      Filter.atTop (nhds 1) := by
  sorry

end MarkovMixing
