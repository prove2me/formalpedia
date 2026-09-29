-- Prove2me | Theorems.Thm_MarkovMixing_hypercube_lower_bound
-- name    : MarkovMixing.hypercube_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:25:36.888949+00:00
-- url     : https://prove2.me/theorems/4cae619a-0ad0-4062-beb3-dd2635780078
-- title:
--   Proposition 7.13 -- lower bound for the lazy hypercube walk
-- statement:
--   The **lazy random walk on the $n$-dimensional hypercube** has state space $\{0,1\}^n$; at each step it stays put with probability $\tfrac12$ and otherwise flips a uniformly chosen coordinate. Its stationary distribution is uniform. Write $P^t(x,\cdot)$ for the law at time $t$ started at $x$, $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ for the total variation distance, and $d(t)=\max_x\|P^t(x,\cdot)-\mathrm{unif}\|_{TV}$.
--
--   The theorem (Proposition 7.13 of Levin–Peres–Wilmer) asserts: for every $n\ge2$, every $\alpha>0$, and every integer time
--   $$t\;\le\;\tfrac12\,n\log n-\alpha n,\qquad\text{one has}\qquad d(t)\;\ge\;1-8\,e^{\,1-2\alpha}.$$
--   So slightly before time $\tfrac12 n\log n$ the walk is still essentially unmixed. The distinguishing statistic is the Hamming weight: started at the all-ones vertex, the number of ones stays measurably above its equilibrium level until the last slow coordinates have been refreshed. Combined with the matching upper bound, this pins the hypercube's mixing time at $\tfrac12 n\log n$ to leading order.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 7.3.1, Proposition 7.13, p. 95

import Definitions.Def_mm_lower
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Proposition 7.13** (LPW): for the lazy random walk on the
`n`-dimensional hypercube, `d(½ n log n − α n) ≥ 1 − 8 e^{-2α+1}`.  (Stated
for every integer time `t ≤ ½ n log n − α n`.) -/
theorem hypercube_lower_bound (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α)
    (t : ℕ) (ht : (t : ℝ) ≤ 2⁻¹ * n * Real.log n - α * n) :
    1 - 8 * Real.exp (1 - 2 * α) ≤
      distStationary (hypercubeWalk n) (uniformDist (Fin n → ZMod 2)) t := by
  sorry

end MarkovMixing
