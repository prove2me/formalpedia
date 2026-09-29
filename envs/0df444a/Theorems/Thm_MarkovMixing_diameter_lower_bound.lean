-- Prove2me | Theorems.Thm_MarkovMixing_diameter_lower_bound
-- name    : MarkovMixing.diameter_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:24:38.737747+00:00
-- url     : https://prove2.me/theorems/5060dbfd-3aac-4180-aad0-e9d92cd97828
-- title:
--   Section 7.1.2 -- the diameter bound
-- statement:
--   Let $P$ be an irreducible, aperiodic Markov chain on a finite state space $V$ with stationary distribution $\pi$. The **transition graph** of $P$ joins two distinct states $x\ne y$ whenever the chain can cross between them in one step in either direction ($P(x,y)>0$ or $P(y,x)>0$); write $\rho(x,y)$ for the graph distance in this graph — the least number of steps needed to travel from $x$ to $y$. For a tolerance $\varepsilon$, the **mixing time** $t_{\mathrm{mix}}(\varepsilon)$ is the first $t$ with $\max_x\|P^t(x,\cdot)-\pi\|_{TV}\le\varepsilon$, where $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$.
--
--   The theorem (the diameter bound, §7.1.2, display (7.3) of Levin–Peres–Wilmer) asserts: for every tolerance $\varepsilon<\tfrac12$ and every pair of states $x_0,y_0$,
--   $$\rho(x_0,y_0)\;\le\;2\,t_{\mathrm{mix}}(\varepsilon).$$
--   Equivalently, the mixing time is at least half the diameter of the transition graph: started at two states at distance $\rho$, for $t<\rho/2$ the two time-$t$ distributions occupy disjoint balls and cannot both be within $\varepsilon<\tfrac12$ of the same $\pi$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 7.1.2, Eq. (7.3), p. 88

import Definitions.Def_mm_lower

namespace MarkovMixing

/-- **§7.1.2, Eq. (7.3)** (LPW), the diameter bound: for `ε < 1/2`, the
mixing time is at least half the graph distance between any two states (in
particular, at least half the diameter of the chain). -/
theorem diameter_lower_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (hap : Aperiodic P) (π : V → ℝ) (hπ : IsStationary P π)
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2) (x₀ y₀ : V) :
    (transGraph P).dist x₀ y₀ ≤ 2 * mixingTime P π ε := by
  sorry

end MarkovMixing
