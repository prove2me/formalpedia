-- Prove2me | Theorems.Thm_MarkovMixing_random_map_representation
-- name    : MarkovMixing.random_map_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:45:21.938282+00:00
-- url     : https://prove2.me/theorems/a328d51a-00eb-411a-8210-08a965852293
-- title:
--   Every chain has a random mapping representation
-- statement:
--   Let $P$ be a Markov chain on a finite state space $V$ (nonnegative entries, rows summing to one). A **random mapping representation** of $P$ is a probability distribution $\nu$ on update functions $f:V\to V$ that reproduces the transition probabilities in one step:
--   $$\nu\{f:\ f(x)=y\}\;=\;P(x,y)\qquad\text{for all states }x,y.$$
--   Drawing $f\sim\nu$ and applying it to the current state — whatever that state is — performs one step of the chain from every state simultaneously.
--
--   The theorem (Proposition 1.5 of Levin–Peres–Wilmer, used in Chapter 22) asserts: **every** finite Markov chain has a random mapping representation.
--
--   The construction slices a uniform random variable: partition $[0,1]$ into intervals of lengths $P(x,\cdot)$ for each $x$, and let the update map send each $x$ to the state whose interval contains the draw. Representations are far from unique, and the choice matters enormously in practice — monotone representations are what make monotone CFTP work — but existence is what the correctness theorem of this mission consumes: it guarantees that coupling from the past applies to any finite chain.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 1.2, Proposition 1.5 (used in Section 22.3), p. 7

import Definitions.Def_mm_cftp

namespace MarkovMixing

/-- **Proposition 1.5 / §22.3** (LPW): every finite Markov chain has a
random mapping representation: there is a distribution `ν` on update
functions with `ν{f : f(x) = y} = P(x,y)` for all `x, y`. -/
theorem random_map_representation {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (P : Matrix V V ℝ) (hP : IsStochastic P) :
    ∃ ν : (V → V) → ℝ, IsRandomMapRep P ν := by
  sorry

end MarkovMixing
