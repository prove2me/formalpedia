-- Prove2me | Theorems.Thm_MarkovMixing_graph_walk_reversible
-- name    : MarkovMixing.graph_walk_reversible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:42:47.384864+00:00
-- url     : https://prove2.me/theorems/1d42caf9-0b22-46f8-b78d-2eed08a12d9d
-- title:
--   Examples 1.12 and 1.20 -- simple random walk on a graph
-- statement:
--   On a finite graph with no isolated vertices, simple random walk (move to a uniformly chosen neighbour) is a Markov chain; the distribution $$\pi(x)=\frac{\deg(x)}{2|E|}$$ satisfies detailed balance with it, and is therefore its stationary distribution.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Sections 1.4-1.6, Examples 1.12 and 1.20, pp. 10 and 15

import Definitions.Def_mm_basic

namespace MarkovMixing

/-- **Examples 1.12 and 1.20** (LPW): on a graph with no isolated vertices,
simple random walk is a Markov chain, the distribution
`π(x) = deg(x) / 2|E|` satisfies detailed balance, and it is stationary. -/
theorem graph_walk_reversible {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ x : V, 0 < G.degree x) :
    IsStochastic (graphWalk G) ∧
    DetailedBalance (graphWalk G)
      (fun x => (G.degree x : ℝ) / (2 * G.edgeFinset.card)) ∧
    IsStationary (graphWalk G)
      (fun x => (G.degree x : ℝ) / (2 * G.edgeFinset.card)) := by
  sorry

end MarkovMixing
