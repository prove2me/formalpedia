-- Prove2me | Theorems.Thm_MarkovMixing_glauber_stationary
-- name    : MarkovMixing.glauber_stationary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T15:15:03.953441+00:00
-- url     : https://prove2.me/theorems/ccb5e9c1-06c2-411f-a459-e24de3bfa65c
-- title:
--   Section 3.3.2 -- stationarity of the Glauber dynamics
-- statement:
--   Let $\pi$ be a probability distribution on the space of configurations $x:\mathcal V\to S$, which assign a spin from a finite set $S$ to each site of a finite nonempty set $\mathcal V$. The **Glauber dynamics** (single-site heat bath) for $\pi$ makes one step as follows: pick a site $v$ uniformly at random, and replace the spin at $v$ by a sample from $\pi$ conditioned on agreeing with the current configuration at every site other than $v$.
--
--   The theorem asserts four things about the resulting transition matrix $G$. First, all entries are nonnegative. Second, for every configuration $x$ in the **support** of $\pi$ (i.e. with $\pi(x)>0$) the row of $G$ at $x$ sums to one — so restricted to the support, $G$ is a genuine Markov chain. (Positivity of $\pi$ is *not* assumed, and at a configuration of zero mass the conditioning that defines a step can be vacuous, so row sums are claimed only on the support.) Third, $G$ satisfies the **detailed balance** equations $\pi(x)\,G(x,y)=\pi(y)\,G(y,x)$ for all configurations $x,y$ — reversibility with respect to $\pi$. Fourth, $\pi$ is a **stationary distribution**: $\sum_x\pi(x)\,G(x,y)=\pi(y)$ for every $y$. This is Exercise 3.2 (§3.3.2) of Levin–Peres–Wilmer.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 3.3.2, Eq. (3.6) and Exercise 3.2, pp. 41-42

import Definitions.Def_mm_mcmc

namespace MarkovMixing

/-- **§3.3.2, Exercise 3.2** (LPW): the Glauber dynamics for a distribution
`π` on configurations is reversible with respect to `π` and has stationary
distribution `π`; its entries are nonnegative and every row at a
configuration in the support of `π` sums to `1`. -/
theorem glauber_stationary {Vv S : Type*} [Fintype Vv] [DecidableEq Vv]
    [Fintype S] [DecidableEq S] [Nonempty Vv]
    (π : (Vv → S) → ℝ) (hπ : IsDist π) :
    (∀ x y : Vv → S, 0 ≤ glauber π x y) ∧
    (∀ x : Vv → S, 0 < π x → ∑ y, glauber π x y = 1) ∧
    DetailedBalance (glauber π) π ∧
    IsStationary (glauber π) π := by
  sorry

end MarkovMixing
