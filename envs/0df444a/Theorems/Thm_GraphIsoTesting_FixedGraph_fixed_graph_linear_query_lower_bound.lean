-- Prove2me | Theorems.Thm_GraphIsoTesting_FixedGraph_fixed_graph_linear_query_lower_bound
-- name    : GraphIsoTesting.FixedGraph.fixed_graph_linear_query_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:32:00.628976+00:00
-- url     : https://prove2.me/theorems/932bf999-8a52-476a-9c90-d67cc06262cf
-- title:
--   Theorem 1.1 — Linear query lower bound for fixed-graph isomorphism
-- statement:
--   There are constants $\varepsilon_0>0$ and $c>0$, a natural threshold $n_0$, and a family of known simple graphs $H_n$ on exactly $n$ vertices such that, for every $n\ge n_0$, $H_n$ has maximum degree at most 13 and every randomized adaptive $\varepsilon_0$-tester for isomorphism to $H_n$, with worst-case query cap $q$, satisfies
--
--   $$q\ge cn.$$
--
--   The tester accepts every isomorphic graph and rejects every graph with $\operatorname{dist}_{\rm iso}(G,H_n)>\varepsilon_0 n\cdot13/2$, each with probability at least $2/3$, for every valid incidence ordering. The unknown input may be any graph of the degree bound. The tester has full knowledge of its target and unrestricted offline computation. All constants and the family precede the universal size and tester quantifiers.
--
--   The degree witness 13 is supplied by Remark 1.3 and p. 9. For the all-size proof, take a common $0<\delta<1$ from Lemma 2.3 and use Theorem 2.2 with $\rho=1/2$ to obtain $\beta>0$. With $d=13$ and $K=(1+4d)^2$, §3.5 gives $\varepsilon_{\rm core}=2\beta/(13dK)$. A degree-preserving realization of Remark 3.7 pads the $13\lfloor n/13\rfloor$-vertex core with $n\bmod13\le12$ isolated vertices; uniform witnesses are $\varepsilon_0=\beta/(26dK)$ and $c=\delta/13$. The threshold absorbs the earlier system thresholds, $n\ge24$, and $4d\cdot12\le\beta m/(2K)$ for $m=2\lfloor n/13\rfloor$. These are witness choices, not extra promises on inputs, and the theorem keeps its constants existential.
--
--   This is the full arbitrary-size headline theorem, with no restriction to multiples of 13 and no one-sided or nonadaptive tester limitation.
--
--   Differences from the source:
--   - generalization: there exists a constant degree bound d → the degree bound is fixed to 13; reason: Remark 1.3 and the construction on p. 9 supply this witness, which implies the printed existential d claim
--   - encoding: randomized adaptive incidence testers, Ω(n), and sufficiently large graph sizes → PMF response trees with explicit uniform positive constants and a natural threshold on Fin n; reason: this represents arbitrary maximum-query algorithms, preserves the strict edge-distance promise and success 2/3, and includes all sufficiently large n
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), p. 2, Theorem 1.1 and Remark 1.3; p. 14, §3.5 and Remark 3.7

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_GraphModel

namespace GraphIsoTesting.FixedGraph

theorem fixed_graph_linear_query_lower_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∃ H : (n : ℕ) → SimpleGraph (Fin n), ∀ n : ℕ, n₀ ≤ n →
        DegreeBound (H n) 13 ∧
        ∀ (q : ℕ) (T : RandomizedTester (Fin n × Fin 13) (Option (Fin n)) q),
          IsGraphTester (H n) 13 ε₀ T → c * (n : ℝ) ≤ (q : ℝ) := by sorry

end GraphIsoTesting.FixedGraph
