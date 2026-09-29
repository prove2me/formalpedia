-- Prove2me | Theorems.Thm_MetricTSP_tour_of_parity_join
-- name    : MetricTSP.tour_of_parity_join
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T21:31:12.820183+00:00
-- url     : https://prove2.me/theorems/1c6796ab-554d-488d-94ae-4c03a5b62fde
-- title:
--   Euler tour and shortcut: connected plus odd-degree pairing yields a tour
-- statement:
--   **The Christofides glue.** Let $G$ be a connected graph on the $n \ge 3$ cities, and let $f$ be an involution of the cities whose non-fixed points are exactly the vertices of odd degree in $G$ --- i.e., $f$ encodes a perfect matching $M$ on the odd-degree set $T$ of $G$ (a matching of all of $T$ exists as an abstract pairing since $|T|$ is even by the handshake lemma; $f$ is one such pairing). Then there is a Hamiltonian tour of cost at most
--   $$\mathrm{tourCost}(c,\pi) \;\le\; \mathrm{cost}(G) + \mathrm{cost}(M), \qquad \mathrm{cost}(M) = \tfrac12\sum_v c(v, f(v)).$$
--
--   The multigraph $G + M$ (an edge of $M$ parallel to an edge of $G$ is taken with multiplicity two) has every degree even and is connected, hence is Eulerian; walking an Euler tour and shortcutting repeated cities with the triangle inequality yields a Hamiltonian cycle that pays each edge of $G$ and each matching edge at most once. This is the assembly step of Christofides' algorithm and of Wolsey's LP-relative analysis: applied to a cheap connected subgraph and a cheap parity-correcting matching it gives a tour of cost at most $\tfrac32$ times the Held--Karp objective.
-- source:
--   N. Christofides, Worst-case analysis of a new heuristic for the travelling salesman problem, Report 388, GSIA, Carnegie Mellon University, 1976; D. P. Williamson, D. B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press 2011, Theorem 2.13 (Christofides' algorithm: Euler tour of tree plus matching, then shortcut).

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_graph_cost

namespace MetricTSP

theorem tour_of_parity_join (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.Connected) (f : Fin n → Fin n) (hinv : ∀ v, f (f v) = v)
    (hodd : ∀ v, f v ≠ v ↔ Odd (G.degree v)) :
    ∃ π : Equiv.Perm (Fin n),
      tourCost c π ≤ graphCost c G + (1 / 2) * ∑ v, c v (f v) := by sorry

end MetricTSP
