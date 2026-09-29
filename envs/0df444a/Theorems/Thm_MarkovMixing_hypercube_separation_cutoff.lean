-- Prove2me | Theorems.Thm_MarkovMixing_hypercube_separation_cutoff
-- name    : MarkovMixing.hypercube_separation_cutoff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:28:20.809455+00:00
-- url     : https://prove2.me/theorems/2edab7db-00d0-49ed-abb8-a90f6632fb53
-- title:
--   Hypercube separation cutoff at $n\log n$
-- statement:
--   The **lazy random walk on the $n$-dimensional hypercube** has state space $\{0,1\}^n$; at each step it stays put with probability $\tfrac12$ and otherwise flips a uniformly chosen coordinate; its stationary distribution is uniform. The **maximal separation distance** at time $t$ is
--   $$s_n(t)=\max_{x,y}\Bigl(1-\frac{P^t_n(x,y)}{u(y)}\Bigr),\qquad u\ \text{the uniform distribution},$$
--   which vanishes only when every transition probability has reached its uniform value (Mission III). A family has a **separation cutoff at $t_n$ with window $w_n$** when $w_n/t_n\to0$ and $s_n(\lfloor t_n+\alpha w_n\rfloor)$ tends (in the liminf/limsup sense) to $1$ as $\alpha\to-\infty$ and to $0$ as $\alpha\to+\infty$.
--
--   The theorem (Theorem 18.8 of Levin–Peres–Wilmer) asserts: the lazy hypercube walk has a separation cutoff at
--   $$t_n=n\log n\qquad\text{with window}\qquad w_n=n.$$
--
--   Separation converges abruptly too — but at $n\log n$, **twice** the total-variation cutoff time $\tfrac12n\log n$ of the companion theorem. The pair is the standard example that the two notions of mixing genuinely differ at the level of constants. The upper bound comes from the coordinate-refresh strong stationary time (all $n$ coordinates updated, a full coupon collection); the lower bound tracks the probability that some coordinate is still unrefreshed.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 18.4, Theorem 18.8, p. 254

import Definitions.Def_mm_cutoff
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Theorem 18.8** (LPW): the lazy random walk on the `n`-dimensional
hypercube has a *separation* cutoff at `n log n` with a window of order
`n`. -/
theorem hypercube_separation_cutoff :
    HasSepCutoffWindow (fun n => hypercubeWalk n)
      (fun n => uniformDist (Fin n → ZMod 2))
      (fun n => n * Real.log n) (fun n => n) := by
  sorry

end MarkovMixing
