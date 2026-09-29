-- Prove2me | Theorems.Thm_MetricTSP_eliminate_steiner2
-- name    : MetricTSP.eliminate_steiner2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T23:52:47.456096+00:00
-- url     : https://prove2.me/theorems/ee2473b7-ca78-443f-949c-1ee5db64019b
-- title:
--   Splitting off the Steiner vertices of a regular even multigraph
-- statement:
--   **Lovász splitting-off, metric form.** Let $H$ be a $2N$-regular multigraph (a symmetric multiplicity function with zero diagonal and every degree exactly $2N$) on the cities, let $T$ be a set of at least two terminals, and suppose every cut separating two terminals has at least $2N$ edges. Then all the non-terminal (*Steiner*) vertices can be split off: there is a multigraph $H'$ whose edges lie inside $T$, with degree exactly $2N$ at every terminal, still with every terminal-separating cut of size at least $2N$, and, since splitting a path $u{-}v{-}w$ into the edge $u{-}w$ does not increase metric cost, with\n$$\sum_{u,v} H'(u,v)\,c(u,v) \le \sum_{u,v} H(u,v)\,c(u,v).$$\n\nThe combinatorial core is **Lovász's splitting-off lemma** in its Eulerian, uniform-demand form: at a vertex $v$ of even degree, some pair of edges at $v$ can be replaced by their shortcut while preserving all terminal-separating cuts at level $2N$. In an even multigraph every cut is even, so every *dangerous* set (a terminal-separating set not containing $v$ whose cut is at most $2N+1$) is in fact tight at $2N$; if every pair of neighbours of $v$ were blocked by a dangerous set, then taking a maximal dangerous set $X$, a neighbour $w
--   otin X$ (no dangerous set contains all neighbours, since adding $v$ to it would drop its cut below $2N$), and a dangerous set $Y$ covering a blocked pair through $X \cap Y$, the two submodular cut identities force either a dangerous set strictly above the maximal $X$ or a vanishing edge count $d(X \cap Y, \overline{X \cup Y}) = 0$ contradicting the edge from $v$ into $X \cap Y$. Parallel pairs at a non-terminal neighbour are simply deleted; parallel pairs at a terminal neighbour can always be traded for a genuine split, preserving terminal degrees. Iterating drives every Steiner degree to zero.\n\nCombined with `MetricTSP.even_set_matching` on the resulting terminal-supported multigraph, this supplies the parity-correction matching (`MetricTSP.parity_matching`) of Wolsey's $\tfrac32$ analysis.
-- source:
--   L. Lovász, On some connectivity properties of Eulerian graphs, Acta Mathematica Academiae Scientiarum Hungaricae 28 (1976) 129-138, https://doi.org/10.1007/BF01902503 (the Eulerian splitting-off lemma); A. Frank, Connections in Combinatorial Optimization, Oxford University Press 2011, Chapter 8 (splitting-off techniques).

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem eliminate_steiner2 (n : ℕ) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (T : Finset (Fin n)) (hT2 : 2 ≤ T.card) (N : ℕ) (hN : 1 ≤ N)
    (H : Fin n → Fin n → ℕ) (hsym : ∀ u v, H u v = H v u) (hdiag : ∀ v, H v v = 0)
    (hdeg : ∀ v, ∑ u, H v u = 2 * N)
    (hcut : ∀ S : Finset (Fin n), (S ∩ T).Nonempty → (Sᶜ ∩ T).Nonempty →
      2 * N ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, H u v) :
    ∃ H' : Fin n → Fin n → ℕ, (∀ u v, H' u v = H' v u) ∧ (∀ v, H' v v = 0) ∧
      (∀ u v, H' u v ≠ 0 → u ∈ T ∧ v ∈ T) ∧
      (∀ v ∈ T, ∑ u, H' v u = 2 * N) ∧
      (∀ S : Finset (Fin n), (S ∩ T).Nonempty → (Sᶜ ∩ T).Nonempty →
        2 * N ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, H' u v) ∧
      ∑ u, ∑ v, (H' u v : ℝ) * c u v ≤ ∑ u, ∑ v, (H u v : ℝ) * c u v := by sorry

end MetricTSP
